import Chess.RulesComplete
import Chess.SemanticBasicLegalLemmas
import Chess.SemanticPieceTargetsCompletenessLemmas
import Chess.SemanticPawnPieceTargetsCompletenessLemmas
import Chess.SemanticCastlingPieceTargetsCompletenessLemmas

namespace Chess
namespace Rules

open Movement

private theorem absInt_eq_one_of_le_one_of_ne_zero (x : Int) :
    Movement.absInt x ≤ 1 →
    x ≠ 0 →
    Movement.absInt x = 1 := by
  intro hLe hNe
  cases x with
  | ofNat n =>
      cases n with
      | zero =>
          cases (hNe rfl)
      | succ n =>
          cases n with
          | zero =>
              simp [Movement.absInt]
          | succ n =>
              -- `n+2 ≤ 1` is impossible.
              have hInt : Int.ofNat (Nat.succ (Nat.succ n)) ≤ (Int.ofNat 1) := by
                simpa [Movement.absInt] using hLe
              have hNat : Nat.succ (Nat.succ n) ≤ 1 := (Int.ofNat_le).1 hInt
              have h2 : 2 ≤ Nat.succ (Nat.succ n) :=
                Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
              have h21 : ¬(2 ≤ 1) := by decide
              cases (h21 (Nat.le_trans h2 hNat))
  | negSucc n =>
      cases n with
      | zero =>
          simp [Movement.absInt]
      | succ n =>
          have hInt : Int.ofNat (Nat.succ (Nat.succ n)) ≤ (Int.ofNat 1) := by
            simpa [Movement.absInt] using hLe
          have hNat : Nat.succ (Nat.succ n) ≤ 1 := (Int.ofNat_le).1 hInt
          have h2 : 2 ≤ Nat.succ (Nat.succ n) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
          have h21 : ¬(2 ≤ 1) := by decide
          cases (h21 (Nat.le_trans h2 hNat))

theorem fideLegalSemantic_implies_respectsPin_of_not_knight (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    m.piece.pieceType ≠ PieceType.Knight →
    respectsPin (pinnedSquares gs gs.toMove) m = true := by
  intro hSem hNotKnight
  rcases hSem with
    ⟨_hTurn, hFrom, hGeom, _hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, _hRookFields⟩
  unfold respectsPin
  cases hFind : (pinnedSquares gs gs.toMove).find? (fun p => p.fst = m.fromSq) with
  | none =>
      simp
  | some pk =>
      -- If we're in the pinned branch, show the move stays on a rook/diagonal line.
      have hAligned : Movement.fileDiff m.fromSq m.toSq = 0 ∨
          Movement.rankDiff m.fromSq m.toSq = 0 ∨
          Movement.absInt (Movement.fileDiff m.fromSq m.toSq) =
            Movement.absInt (Movement.rankDiff m.fromSq m.toSq) := by
        cases hpt : m.piece.pieceType with
        | Knight =>
            cases hNotKnight (by simp [hpt])
        | King =>
            -- King
          -- (We only need the “line-shaped” property; any king move is either on a rank/file or a diagonal.)
          by_cases hCastle : m.isCastle
          ·
            -- For castling, `rankDiff = 0` (king moves horizontally).
            have hCastleGeom :
                ∃ cfg : CastleConfig,
                  cfg.kingFrom = m.fromSq ∧
                    cfg.kingTo = m.toSq ∧
                      (cfg = castleConfig m.piece.color true ∨
                        cfg = castleConfig m.piece.color false) := by
              simpa [respectsGeometry, hpt, hCastle] using hGeom
            rcases hCastleGeom with ⟨cfg, hCfgFrom, hCfgTo, hCfg⟩
            have hRank : Movement.rankDiff m.fromSq m.toSq = 0 := by
              cases hCfg with
              | inl hEq =>
                  subst hEq
                  have hFrom' : m.fromSq = (castleConfig m.piece.color true).kingFrom := by
                    simpa using hCfgFrom.symm
                  have hTo' : m.toSq = (castleConfig m.piece.color true).kingTo := by
                    simpa using hCfgTo.symm
                  cases hColor : m.piece.color <;>
                    (simp [hColor, hFrom', hTo', Movement.rankDiff, castleConfig] <;> decide)
              | inr hEq =>
                  subst hEq
                  have hFrom' : m.fromSq = (castleConfig m.piece.color false).kingFrom := by
                    simpa using hCfgFrom.symm
                  have hTo' : m.toSq = (castleConfig m.piece.color false).kingTo := by
                    simpa using hCfgTo.symm
                  cases hColor : m.piece.color <;>
                    (simp [hColor, hFrom', hTo', Movement.rankDiff, castleConfig] <;> decide)
            exact Or.inr (Or.inl hRank)
          ·
            have hStep : Movement.isKingStep m.fromSq m.toSq := by
              simpa [respectsGeometry, hpt, hCastle] using hGeom
            -- If either delta is 0 we're done; otherwise abs deltas are equal (both are 1).
            by_cases hfd0 : Movement.fileDiff m.fromSq m.toSq = 0
            · exact Or.inl hfd0
            · by_cases hrd0 : Movement.rankDiff m.fromSq m.toSq = 0
              · exact Or.inr (Or.inl hrd0)
              ·
                have hfd : Movement.absInt (Movement.fileDiff m.fromSq m.toSq) = 1 := by
                  exact absInt_eq_one_of_le_one_of_ne_zero
                    (Movement.fileDiff m.fromSq m.toSq) hStep.2.1 hfd0
                have hrd : Movement.absInt (Movement.rankDiff m.fromSq m.toSq) = 1 := by
                  exact absInt_eq_one_of_le_one_of_ne_zero
                    (Movement.rankDiff m.fromSq m.toSq) hStep.2.2 hrd0
                exact Or.inr (Or.inr (by simp [hfd, hrd]))
        | Queen =>
            -- Queen
          have hGeomQ : Movement.isQueenMove m.fromSq m.toSq ∧ pathClear gs.board m.fromSq m.toSq = true := by
            simpa [respectsGeometry, hpt] using hGeom
          have hQ : Movement.isQueenMove m.fromSq m.toSq := hGeomQ.1
          cases hQ with
          | inl hR =>
              cases (Movement.rook_move_straight (source := m.fromSq) (target := m.toSq) hR) with
              | inl hf => exact Or.inl hf
              | inr hr => exact Or.inr (Or.inl hr)
          | inr hD =>
              exact Or.inr (Or.inr hD.2)
        | Rook =>
            -- Rook
          have hGeomR : Movement.isRookMove m.fromSq m.toSq ∧ pathClear gs.board m.fromSq m.toSq = true := by
            simpa [respectsGeometry, hpt] using hGeom
          have hR : Movement.isRookMove m.fromSq m.toSq := hGeomR.1
          cases (Movement.rook_move_straight (source := m.fromSq) (target := m.toSq) hR) with
          | inl hf => exact Or.inl hf
          | inr hr => exact Or.inr (Or.inl hr)
        | Bishop =>
            -- Bishop
          have hGeomB : Movement.isDiagonal m.fromSq m.toSq ∧ pathClear gs.board m.fromSq m.toSq = true := by
            simpa [respectsGeometry, hpt] using hGeom
          have hD : Movement.isDiagonal m.fromSq m.toSq := hGeomB.1
          exact Or.inr (Or.inr hD.2)
        | Pawn =>
            -- Pawn
          by_cases hCap : m.isCapture
          ·
            by_cases hEP : m.isEnPassant
            ·
              have hCapGeom :
                  Movement.isPawnCapture m.piece.color m.fromSq m.toSq ∧
                    gs.enPassantTarget = some m.toSq ∧
                    isEmpty gs.board m.toSq = true ∧
                    enPassantFromHistory gs m.toSq = true := by
                simpa [respectsGeometry, hpt, hCap, hEP] using hGeom
              have hPC : Movement.isPawnCapture m.piece.color m.fromSq m.toSq := hCapGeom.1
              -- Pawn captures are diagonal.
              right
              right
              have hf : Movement.absInt (Movement.fileDiff m.fromSq m.toSq) = 1 := hPC.2.1
              have hr : Movement.absInt (Movement.rankDiff m.fromSq m.toSq) = 1 := by
                -- `rankDiff = -pawnDirection` so abs is 1.
                have hrd : Movement.rankDiff m.fromSq m.toSq = -Movement.pawnDirection m.piece.color := hPC.2.2
                cases hColor : m.piece.color <;>
                  simp [Movement.pawnDirection, Movement.absInt, hColor] at hrd ⊢ <;>
                  simp [hrd]
              simp [hf, hr]
            ·
              have hCapGeom :
                  Movement.isPawnCapture m.piece.color m.fromSq m.toSq ∧
                    isEnemyAt gs.board m.piece.color m.toSq = true := by
                simpa [respectsGeometry, hpt, hCap, hEP] using hGeom
              have hPC : Movement.isPawnCapture m.piece.color m.fromSq m.toSq := hCapGeom.1
              right
              right
              have hf : Movement.absInt (Movement.fileDiff m.fromSq m.toSq) = 1 := hPC.2.1
              have hr : Movement.absInt (Movement.rankDiff m.fromSq m.toSq) = 1 := by
                have hrd : Movement.rankDiff m.fromSq m.toSq = -Movement.pawnDirection m.piece.color := hPC.2.2
                cases hColor : m.piece.color <;>
                  simp [Movement.pawnDirection, Movement.absInt, hColor] at hrd ⊢ <;>
                  simp [hrd]
              simp [hf, hr]
          ·
            have hQuiet :
                Movement.isPawnAdvance m.piece.color m.fromSq m.toSq ∧
                  pathClear gs.board m.fromSq m.toSq = true ∧
                    (Movement.rankDiff m.fromSq m.toSq =
                          -2 * Movement.pawnDirection m.piece.color →
                        m.fromSq.rankNat = pawnStartRank m.piece.color) := by
              simpa [respectsGeometry, hpt, hCap] using hGeom
            -- Pawn advances stay on file.
            have : Movement.fileDiff m.fromSq m.toSq = 0 := hQuiet.1.2.1
            exact Or.inl this
      -- Convert alignment into the Bool/decide form used by `respectsPin`.
      let fd := Movement.absInt (Movement.fileDiff m.fromSq m.toSq)
      let rd := Movement.absInt (Movement.rankDiff m.fromSq m.toSq)
      have hGoal : fd = 0 ∨ rd = 0 ∨ fd = rd := by
        cases hAligned with
        | inl hf =>
            left
            simp [fd, Movement.absInt, hf]
        | inr hRest =>
            cases hRest with
            | inl hr =>
                right
                left
                simp [rd, Movement.absInt, hr]
            | inr hEq =>
                right
                right
                simpa [fd, rd] using hEq
      have : decide (fd = 0 ∨ rd = 0 ∨ fd = rd) = true := by
        exact Eq.mp (decide_eq_true_eq (p := fd = 0 ∨ rd = 0 ∨ fd = rd)).symm hGoal
      cases hpt : m.piece.pieceType with
      | Knight =>
          cases hNotKnight (by simp [hpt])
      | _ =>
          simpa [fd, rd, hFind, hpt] using this

theorem fideLegalSemantic_implies_respectsPin (gs : GameState) (m : Move) :
    fideLegalSemantic gs m →
    respectsPin (pinnedSquares gs gs.toMove) m = true := by
  intro hSem
  by_cases hKnight : m.piece.pieceType = PieceType.Knight
  · unfold respectsPin
    cases hFind : (pinnedSquares gs gs.toMove).find? (fun p => p.fst = m.fromSq) <;>
      simp [hKnight]
  · exact fideLegalSemantic_implies_respectsPin_of_not_knight gs m hSem hKnight

theorem fideLegalSemantic_implies_mem_allLegalMoves_of_not_knight (gs : GameState) (m : Move) :
    hasValidEPRank gs →
    fideLegalSemantic gs m →
    m.piece.pieceType ≠ PieceType.Knight →
    m ∈ allLegalMoves gs := by
  intro hEP hSem hNotKnight
  have hSem0 := hSem
  rcases hSem with
    ⟨hTurn, hFrom, _hGeom, _hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, _hRookFields⟩
  have hSafe : basicLegalAndSafe gs m = true :=
    fideLegalSemantic_implies_basicLegalAndSafe gs m hSem0
  have hPin : respectsPin (pinnedSquares gs gs.toMove) m = true :=
    fideLegalSemantic_implies_respectsPin_of_not_knight gs m hSem0 hNotKnight
  have hTargets : m ∈ pieceTargets gs m.fromSq m.piece := by
    cases hpt : m.piece.pieceType with
    | King =>
        by_cases hCastle : m.isCastle = true
        · exact fideLegalSemantic_implies_mem_pieceTargets_king_castle gs m hSem0 hCastle
        ·
          have hNoCastle : m.isCastle = false := by
            cases hB : m.isCastle with
            | false => rfl
            | true => cases (hCastle hB)
          exact fideLegalSemantic_implies_mem_pieceTargets_king_not_castle gs m hSem0 hpt hNoCastle
    | Queen =>
        exact fideLegalSemantic_implies_mem_pieceTargets_queen gs m hSem0 hpt
    | Rook =>
        exact fideLegalSemantic_implies_mem_pieceTargets_rook gs m hSem0 hpt
    | Bishop =>
        exact fideLegalSemantic_implies_mem_pieceTargets_bishop gs m hSem0 hpt
    | Knight =>
        cases hNotKnight (by simp [hpt])
    | Pawn =>
        exact fideLegalSemantic_implies_mem_pieceTargets_pawn gs m hEP hSem0 hpt
  have hEnc : encodedLegal gs m :=
    ⟨m.fromSq, m.piece, hFrom, hTurn, hTargets, hPin, hSafe⟩
  exact (mem_allLegalMoves_iff_encodedLegal gs m).2 hEnc

theorem fideLegalSemantic_implies_mem_allLegalMoves (gs : GameState) (m : Move) :
    hasValidEPRank gs →
    fideLegalSemantic gs m →
    m ∈ allLegalMoves gs := by
  intro hEP hSem
  have hSem0 := hSem
  rcases hSem with
    ⟨hTurn, hFrom, _hGeom, _hDest, _hCapSpec, _hNotCheck, _hPromoFwd, _hPromoBack, _hCastleClause,
      _hEPFlag, _hCastleFlag, _hRookFields⟩
  have hSafe : basicLegalAndSafe gs m = true :=
    fideLegalSemantic_implies_basicLegalAndSafe gs m hSem0
  have hPin : respectsPin (pinnedSquares gs gs.toMove) m = true :=
    fideLegalSemantic_implies_respectsPin gs m hSem0
  have hTargets : m ∈ pieceTargets gs m.fromSq m.piece := by
    cases hpt : m.piece.pieceType with
    | King =>
        by_cases hCastle : m.isCastle = true
        · exact fideLegalSemantic_implies_mem_pieceTargets_king_castle gs m hSem0 hCastle
        ·
          have hNoCastle : m.isCastle = false := by
            cases hB : m.isCastle with
            | false => rfl
            | true => cases (hCastle hB)
          exact fideLegalSemantic_implies_mem_pieceTargets_king_not_castle gs m hSem0 hpt hNoCastle
    | Queen =>
        exact fideLegalSemantic_implies_mem_pieceTargets_queen gs m hSem0 hpt
    | Rook =>
        exact fideLegalSemantic_implies_mem_pieceTargets_rook gs m hSem0 hpt
    | Bishop =>
        exact fideLegalSemantic_implies_mem_pieceTargets_bishop gs m hSem0 hpt
    | Knight =>
        exact fideLegalSemantic_implies_mem_pieceTargets_knight gs m hSem0 hpt
    | Pawn =>
        exact fideLegalSemantic_implies_mem_pieceTargets_pawn gs m hEP hSem0 hpt
  have hEnc : encodedLegal gs m :=
    ⟨m.fromSq, m.piece, hFrom, hTurn, hTargets, hPin, hSafe⟩
  exact (mem_allLegalMoves_iff_encodedLegal gs m).2 hEnc

end Rules
end Chess
