import Init.Omega
import Chess.Spec
import Chess.Completeness
import Chess.SemanticFideLegalSoundness

namespace Chess
namespace Rules

/-- Simplification lemma for `Except` bind on an error. -/
@[simp] theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e).bind f = Except.error e := by
  rfl

/-- Simplification lemma for `Except` bind on a successful value. -/
@[simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a).bind f = f a := by
  rfl

@[simp] theorem except_bind_error' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := by
  rfl

@[simp] theorem except_bind_ok' {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := by
  rfl

/--
Reachability predicate: `gs` is produced by applying a sequence of legal moves
starting from `standardGameState`.
-/
def reachableFromStandard (gs : GameState) : Prop :=
  ∃ moves : List Move, applyLegalMoves standardGameState moves = Except.ok gs

@[simp] theorem finalizeResult_enPassantTarget (before after : GameState) :
    (finalizeResult before after).enPassantTarget = after.enPassantTarget := by
  unfold finalizeResult
  cases hRes : after.result.isSome <;>
    cases hMate : isCheckmate after <;>
    cases hDraw :
        (isStalemate after || isSeventyFiveMoveDraw after || fivefoldRepetition after ||
          insufficientMaterial after || deadPosition after) <;>
      simp

private theorem Square.mkUnsafe_rankNat (file rank : Nat) (hf : file < 8) (hr : rank < 8) :
    (Square.mkUnsafe file rank).rankNat = rank := by
  unfold Square.mkUnsafe Square.mk?
  simp [hf, hr, Square.rankNat, Rank.toNat]

private theorem pawnAdvance_twoStep_of_natAbs_two
    (c : Color) (src tgt : Square)
    (hAdv : Movement.isPawnAdvance c src tgt)
    (hAbs : Int.natAbs (Movement.rankDiff src tgt) = 2) :
    Movement.rankDiff src tgt = -2 * Movement.pawnDirection c := by
  rcases hAdv with ⟨_hNe, _hFd, hRd⟩
  cases c with
  | White =>
      have hDir : Movement.pawnDirection Color.White = 1 := by
        simp [Movement.pawnDirection]
      have hAbs' : Int.natAbs (Movement.rankDiff src tgt) = 2 := hAbs
      cases hRd with
      | inl h1 =>
          have : Int.natAbs (Movement.rankDiff src tgt) = 1 := by
            simp [h1, hDir]
          cases (show False by simpa [this] using hAbs')
      | inr h2 =>
          simp [h2]
  | Black =>
      have hDir : Movement.pawnDirection Color.Black = -1 := by
        simp [Movement.pawnDirection]
      have hAbs' : Int.natAbs (Movement.rankDiff src tgt) = 2 := hAbs
      cases hRd with
      | inl h1 =>
          have : Int.natAbs (Movement.rankDiff src tgt) = 1 := by
            -- For black, `-pawnDirection = 1`.
            simp [h1, hDir]
          cases (show False by simpa [this] using hAbs')
      | inr h2 =>
          simp [h2]

theorem hasValidEPRank_playMove_of_mem_allLegalMoves (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    hasValidEPRank (GameState.playMove gs m) := by
  intro hMem
  have hGeom : respectsGeometry gs m := allLegalMoves_sound_respectsGeometry gs m hMem
  -- `playMove` does not change the `enPassantTarget` computed by `movePiece`.
  have hPlayEP :
      (GameState.playMove gs m).enPassantTarget = (gs.movePiece m).enPassantTarget := by
    unfold GameState.playMove
    simp
  unfold hasValidEPRank
  -- Rewrite to `gs.movePiece m` and analyze `newEnPassant`.
  simp [hPlayEP]
  by_cases hTwo :
      (m.piece.pieceType = PieceType.Pawn ∧
        Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 2)
  · -- En passant target is computed from the intermediate square.
    have hPawnType : m.piece.pieceType = PieceType.Pawn := hTwo.1
    have hCapFalse : m.isCapture = false := by
      cases hCap : m.isCapture with
      | false => simp
      | true =>
          have hCapGeom :
              Movement.isPawnCapture m.piece.color m.fromSq m.toSq := by
            cases hEP : m.isEnPassant with
            | false =>
                have :
                    Movement.isPawnCapture m.piece.color m.fromSq m.toSq ∧
                      isEnemyAt gs.board m.piece.color m.toSq = true := by
                  simpa [respectsGeometry, hPawnType, hCap, hEP] using hGeom
                exact this.1
            | true =>
                have :
                    Movement.isPawnCapture m.piece.color m.fromSq m.toSq ∧
                      gs.enPassantTarget = some m.toSq ∧
                        isEmpty gs.board m.toSq = true ∧
                        enPassantFromHistory gs m.toSq = true := by
                  simpa [respectsGeometry, hPawnType, hCap, hEP] using hGeom
                exact this.1
          have hAbsOne : Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 1 := by
            rcases hCapGeom with ⟨_hNe, _hFd, hRd⟩
            cases hc : m.piece.color with
            | White =>
                have hRd0 :
                    Movement.rankDiff m.fromSq m.toSq =
                      -Movement.pawnDirection Color.White := by
                  simpa [hc] using hRd
                have hRd' : Movement.rankDiff m.fromSq m.toSq = -1 := by
                  simpa [Movement.pawnDirection] using hRd0
                simp [hRd']
            | Black =>
                have hRd0 :
                    Movement.rankDiff m.fromSq m.toSq =
                      -Movement.pawnDirection Color.Black := by
                  simpa [hc] using hRd
                have hRd' : Movement.rankDiff m.fromSq m.toSq = 1 := by
                  -- For black, `pawnDirection = -1`, so `-pawnDirection = 1`.
                  simpa [Movement.pawnDirection] using hRd0
                simp [hRd']
          have : (1 : Nat) = 2 := by
            simpa [hAbsOne] using hTwo.2
          have hNe : (1 : Nat) ≠ 2 := by decide
          cases (hNe this)
    have hQuiet :
        Movement.isPawnAdvance m.piece.color m.fromSq m.toSq ∧
          pathClear gs.board m.fromSq m.toSq = true ∧
            (Movement.rankDiff m.fromSq m.toSq =
                -2 * Movement.pawnDirection m.piece.color →
              m.fromSq.rankNat = pawnStartRank m.piece.color) := by
      simpa [respectsGeometry, hPawnType, hCapFalse] using hGeom
    have hRankDiff :
        Movement.rankDiff m.fromSq m.toSq =
          -2 * Movement.pawnDirection m.piece.color :=
      pawnAdvance_twoStep_of_natAbs_two m.piece.color m.fromSq m.toSq hQuiet.1 hTwo.2
    have hFromStart : m.fromSq.rankNat = pawnStartRank m.piece.color :=
      hQuiet.2.2 hRankDiff
    let dir : Int := Movement.pawnDirection m.piece.color
    let targetRankInt : Int := m.fromSq.rankInt + dir
    have hNonneg : 0 ≤ targetRankInt := by
      cases hc : m.piece.color with
      | White =>
          have hFrom : m.fromSq.rank.toNat = 1 := by
            simpa [Square.rankNat, pawnStartRank, hc] using hFromStart
          have hEq : targetRankInt = 2 := by
            simp [targetRankInt, dir, Movement.pawnDirection, Square.rankInt, hFrom, hc]
          simp [hEq]
      | Black =>
          have hFrom : m.fromSq.rank.toNat = 6 := by
            simpa [Square.rankNat, pawnStartRank, hc] using hFromStart
          have hEq : targetRankInt = 5 := by
            simp [targetRankInt, dir, Movement.pawnDirection, Square.rankInt, hFrom, hc]
          simp [hEq]
    have hf : m.fromSq.fileNat < 8 := by
      simp [Square.fileNat, File.toNat]
    cases hc : m.piece.color with
    | White =>
        have hFrom : m.fromSq.rank.toNat = 1 := by
          simpa [Square.rankNat, pawnStartRank, hc] using hFromStart
        have hEq : targetRankInt = 2 := by
          simp [targetRankInt, dir, Movement.pawnDirection, Square.rankInt, hFrom, hc]
        have hRank : (Square.mkUnsafe m.fromSq.fileNat (Int.toNat targetRankInt)).rankNat = 2 := by
          have hr : (Int.toNat targetRankInt) < 8 := by
            simp [hEq]
          simpa [hEq] using (Square.mkUnsafe_rankNat m.fromSq.fileNat (Int.toNat targetRankInt) hf hr)
        have hNonnegDir : 0 ≤ m.fromSq.rankInt + Movement.pawnDirection m.piece.color := by
          simpa [targetRankInt, dir] using hNonneg
        have hRankDir :
            (Square.mkUnsafe m.fromSq.fileNat
                  (m.fromSq.rankInt + Movement.pawnDirection m.piece.color).toNat).rankNat =
              2 := by
          simpa [targetRankInt, dir] using hRank
        simp [GameState.movePiece, hTwo, hNonnegDir, hRankDir]
    | Black =>
        have hFrom : m.fromSq.rank.toNat = 6 := by
          simpa [Square.rankNat, pawnStartRank, hc] using hFromStart
        have hEq : targetRankInt = 5 := by
          simp [targetRankInt, dir, Movement.pawnDirection, Square.rankInt, hFrom, hc]
        have hRank : (Square.mkUnsafe m.fromSq.fileNat (Int.toNat targetRankInt)).rankNat = 5 := by
          have hr : (Int.toNat targetRankInt) < 8 := by
            simp [hEq]
          simpa [hEq] using (Square.mkUnsafe_rankNat m.fromSq.fileNat (Int.toNat targetRankInt) hf hr)
        have hNonnegDir : 0 ≤ m.fromSq.rankInt + Movement.pawnDirection m.piece.color := by
          simpa [targetRankInt, dir] using hNonneg
        have hRankDir :
            (Square.mkUnsafe m.fromSq.fileNat
                  (m.fromSq.rankInt + Movement.pawnDirection m.piece.color).toNat).rankNat =
              5 := by
          simpa [targetRankInt, dir] using hRank
        simp [GameState.movePiece, hTwo, hNonnegDir, hRankDir]
  · simp [GameState.movePiece, hTwo]

private theorem applyLegalMove_ok_implies_mem_and_playMove
    (gs : GameState) (m : Move) (gs' : GameState) :
    applyLegalMove gs m = Except.ok gs' →
    m ∈ allLegalMoves gs ∧ gs' = GameState.playMove gs m := by
  intro hOk
  unfold applyLegalMove applyLegalMove? at hOk
  by_cases hLeg : isLegalMove gs m = true
  · simp [hLeg] at hOk
    refine ⟨?_, ?_⟩
    · -- `isLegalMove` is defined as `any (· = m)` over `allLegalMoves`.
      have : legalMove gs m := by
        simp [legalMove, hLeg]
      exact allLegalMoves_complete gs m this
    · cases hOk
      rfl
  · simp [hLeg] at hOk

theorem reachableFromStandard_hasValidEPRank (gs : GameState) :
    reachableFromStandard gs →
    hasValidEPRank gs := by
  intro hReach
  rcases hReach with ⟨moves, hOk⟩
  -- General lemma: successful `applyLegalMoves` preserves `hasValidEPRank`.
  have hasValidEPRank_of_applyLegalMoves_ok :
      ∀ (gs0 : GameState) (moves : List Move) (out : GameState),
        hasValidEPRank gs0 →
        applyLegalMoves gs0 moves = Except.ok out →
        hasValidEPRank out := by
    intro gs0 moves0
    induction moves0 generalizing gs0 with
    | nil =>
        intro out hValid hOk
        cases hOk
        exact hValid
    | cons mv rest ih =>
        intro out hValid hOk
        cases hStep : applyLegalMove gs0 mv with
        | error e =>
            have hErr : applyLegalMoves gs0 (mv :: rest) = (Except.error e) := by
              simp [applyLegalMoves, List.foldlM, hStep]
            have : (Except.error e : Except String GameState) = Except.ok out := by
              simpa [hErr] using hOk
            cases this
        | ok gs1 =>
            have hTail : applyLegalMoves gs1 rest = Except.ok out := by
              simpa [applyLegalMoves, List.foldlM, hStep] using hOk
            have hMemPlay := applyLegalMove_ok_implies_mem_and_playMove gs0 mv gs1 (by simp [hStep])
            have hValid1 : hasValidEPRank gs1 := by
              have hValidPlay : hasValidEPRank (GameState.playMove gs0 mv) :=
                hasValidEPRank_playMove_of_mem_allLegalMoves gs0 mv hMemPlay.1
              simpa [hMemPlay.2] using hValidPlay
            exact ih (gs0 := gs1) (out := out) hValid1 hTail
  exact hasValidEPRank_of_applyLegalMoves_ok standardGameState moves gs
    standardGameState_hasValidEPRank hOk

theorem allLegalMoves_sound_fideLegalSemantic_of_reachable (gs : GameState) (m : Move) :
    reachableFromStandard gs →
    m ∈ allLegalMoves gs →
    fideLegalSemantic gs m := by
  intro hReach hMem
  have hValid : hasValidEPRank gs := reachableFromStandard_hasValidEPRank gs hReach
  exact allLegalMoves_sound_fideLegalSemantic gs m hValid hMem

theorem mem_allLegalMoves_pawn_toPromotionRank_implies_promotion_isSome_of_reachable
    (gs : GameState) (m : Move) :
    reachableFromStandard gs →
    m ∈ allLegalMoves gs →
    m.piece.pieceType = PieceType.Pawn →
    m.toSq.rankNat = pawnPromotionRank m.piece.color →
    m.promotion.isSome = true := by
  intro hReach hMem hPawn hPromo
  have hValid : hasValidEPRank gs := reachableFromStandard_hasValidEPRank gs hReach
  exact mem_allLegalMoves_pawn_toPromotionRank_implies_promotion_isSome gs m hValid hMem hPawn hPromo

end Rules
end Chess
