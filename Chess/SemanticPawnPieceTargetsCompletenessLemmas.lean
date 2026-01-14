import Init.Omega
import Chess.Spec
import Chess.ParsingProofs
import Chess.SemanticPawnTargetsGeometryLemmas
import Chess.SlidingTargetsDeltaLemmas

namespace Chess
namespace Rules

open Movement

private theorem move_eq_pawn_record
    (m : Move) (cap : Bool) :
    m.isCapture = cap →
    m.promotion = none →
    m.isCastle = false →
    m.castleRookFrom = none →
    m.castleRookTo = none →
    m.isEnPassant = false →
    ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := cap } : Move) = m := by
  intro hCap hPromo hCastle hRF hRT hEP
  cases m with
  | mk piece fromSq toSq isCapture promotion isCastle castleRookFrom castleRookTo isEnPassant =>
      cases cap <;> simp at hCap hPromo hCastle hRF hRT hEP
      · simp [hCap, hPromo, hCastle, hRF, hRT, hEP]
      · simp [hCap, hPromo, hCastle, hRF, hRT, hEP]

theorem fideLegalSemantic_implies_mem_pieceTargets_pawn (gs : GameState) (m : Move) :
    hasValidEPRank gs →
    fideLegalSemantic gs m →
    m.piece.pieceType = PieceType.Pawn →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro hValid hSem hPawn
  rcases hSem with
    ⟨_hTurn, _hFrom, hGeom, hDest, hCapSpec, _hNotCheck, hPromoFwd, hPromoBack, _hCastleClause,
      _hEPFlag, hCastleFlag, hRookFields⟩

  have hNoCastle : m.isCastle = false := by
    cases hC : m.isCastle with
    | false => simp [hC]
    | true =>
        have hKing : m.piece.pieceType = PieceType.King := hCastleFlag (by simp [hC])
        have : False := by
          have : (PieceType.Pawn : PieceType) = PieceType.King := by simpa [hPawn] using hKing.symm
          cases this
        cases this

  have hRookNone : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have : ¬m.isCastle := by simp [hNoCastle]
    exact hRookFields this

  let src : Square := m.fromSq
  let tgt : Square := m.toSq
  let p : Piece := m.piece
  let board : Board := gs.board
  let color : Color := p.color
  let dir : Int := Movement.pawnDirection color

  unfold pieceTargets
  simp [hPawn]

  cases hCap : m.isCapture with
  | false =>
      have hCapFalse : m.isCapture = false := by simpa using hCap
      have hNoEnemyOrEP :
          ¬((∃ q, gs.board tgt = some q ∧ q.color ≠ p.color) ∨ m.isEnPassant) := by
        intro hRhs
        have : m.isCapture = true := (hCapSpec).2 hRhs
        cases (show False by simpa [hCapFalse] using this)
      have hEPFalse : m.isEnPassant = false := by
        cases hE : m.isEnPassant with
        | false => rfl
        | true =>
            have : False := by
              apply hNoEnemyOrEP
              exact Or.inr (by simp [hE])
            cases this
      have hToEmpty : gs.board tgt = none := by
        unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
        cases hAt : gs.board tgt with
        | none => rfl
        | some q =>
            have hEnemy : q.color ≠ p.color := by
              by_cases hEq : q.color = p.color
              · have hFalse : destinationFriendlyFree gs m = false := by
                  simp [destinationFriendlyFree, src, tgt, p, hAt, hEq]
                have : False := by
                  have : destinationFriendlyFree gs m = true := hDest
                  cases (show False by simpa [hFalse] using this)
                cases this
              · exact hEq
            have : (∃ q, gs.board tgt = some q ∧ q.color ≠ p.color) := ⟨q, hAt, hEnemy⟩
            have : False := hNoEnemyOrEP (Or.inl this)
            cases this
      have hEmptyTgt : isEmpty board tgt = true := by
        simpa [isEmpty, board, tgt] using hToEmpty

      have hQuietGeom :
          Movement.isPawnAdvance p.color src tgt ∧
            pathClear board src tgt ∧
              (Movement.rankDiff src tgt = -2 * Movement.pawnDirection p.color →
                src.rankNat = pawnStartRank p.color) := by
        simpa [respectsGeometry, hPawn, hCapFalse, src, tgt, p, board] using hGeom
      have hAdv : Movement.isPawnAdvance p.color src tgt := hQuietGeom.1
      have hPC : pathClear board src tgt = true := by
        simpa using hQuietGeom.2.1

      -- `src -> tgt` is rook-like, so `squaresBetween` describes the intermediate squares used by `pathClear`.
      have hFileDiff0 : Movement.fileDiff src tgt = 0 := hAdv.2.1

      cases hAdv.2.2 with
      | inl hRd1 =>
          -- One-step advance.
          have hOne :
              squareFromInts src.fileInt (src.rankInt + dir) = some tgt := by
            have hRankEq : tgt.rankInt = src.rankInt + dir := by
              have : Movement.rankDiff src tgt = -dir := by
                simpa [dir] using hRd1
              unfold Movement.rankDiff at this
              omega
            have hFileEq : tgt.fileInt = src.fileInt := by
              unfold Movement.fileDiff at hFileDiff0
              omega
            have hSqCoords : squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
              Movement.squareFromInts_of_coords tgt
            simpa [hFileEq, hRankEq] using hSqCoords

          let base : Move := { piece := p, fromSq := src, toSq := tgt }
          have hBaseInForward :
              base ∈
                match squareFromInts src.fileInt (src.rankInt + dir) with
                | some target =>
                    if isEmpty board target then
                      [({ piece := p, fromSq := src, toSq := target } : Move)] ++
                        (if src.rankNat = pawnStartRank p.color then
                            match squareFromInts src.fileInt (src.rankInt + 2 * dir) with
                            | some target2 =>
                                if isEmpty board target2 then
                                  [({ piece := p, fromSq := src, toSq := target2 } : Move)]
                                else []
                            | none => []
                          else [])
                    else []
                | none => [] := by
            simp [base, hOne, hEmptyTgt]

          have hMemProm : m ∈ promotionMoves base := by
            cases hProm : m.promotion with
            | none =>
                -- If at promotion rank, semantic demands `promotion.isSome`.
                by_cases hRank : tgt.rankNat = pawnPromotionRank p.color
                ·
                  have : m.promotion.isSome := hPromoFwd ⟨by simpa [p] using hPawn, by simpa [tgt, p] using hRank⟩
                  cases (show False by simpa [hProm] using this)
                ·
                  have hEqMove :
                      ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
                    move_eq_pawn_record m false (by simp [hCapFalse]) (by simp [hProm]) hNoCastle
                      hRookNone.1 hRookNone.2 hEPFalse
                  -- `promotionMoves base = [base]`.
                  have hBaseEq : m = base := by
                    have : base = m := by simpa [base, src, tgt, p] using hEqMove
                    exact this.symm
                  have hPawnBase : base.piece.pieceType = PieceType.Pawn := by
                    simpa [base, p] using hPawn
                  rw [hBaseEq]
                  have hNotPromo :
                      ¬(base.piece.pieceType = PieceType.Pawn ∧
                        base.toSq.rankNat = pawnPromotionRank base.piece.color) := by
                    intro h
                    have : tgt.rankNat = pawnPromotionRank p.color := by
                      simpa [base, tgt, p] using h.2
                    exact hRank this
                  have hPM : promotionMoves base = [base] := by
                    simp [promotionMoves, hNotPromo]
                  simp [hPM]
            | some pt =>
                have hSome : m.promotion.isSome := by simp [hProm]
                have hRank : tgt.rankNat = pawnPromotionRank p.color := (hPromoBack hSome).2.1
                have hPtMem : pt ∈ promotionTargets := (hPromoBack hSome).2.2 pt (by simp [hProm])
                have hEqMove :
                    ({ base with promotion := some pt } : Move) = m := by
                  apply Move.ext <;> simp [base, src, tgt, p, hProm, hCapFalse, hNoCastle, hRookNone.1, hRookNone.2, hEPFalse]
                -- `m` is one of the mapped promotion targets.
                have hPawnBase : base.piece.pieceType = PieceType.Pawn := by
                  simpa [base, p] using hPawn
                have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
                  simpa [base, tgt, p] using hRank
                simp [promotionMoves, hPawnBase, hRankBase, List.mem_map]
                exact ⟨pt, hPtMem, hEqMove⟩
          refine Or.inl ?_
          refine ⟨promotionMoves base, ?_⟩
          refine ⟨?_, hMemProm⟩
          refine ⟨base, ?_, rfl⟩
          exact hBaseInForward
      | inr hRd2 =>
          -- Two-step advance.
          have hStart : src.rankNat = pawnStartRank p.color := hQuietGeom.2.2 hRd2
          have hRook : Movement.isRookMove src tgt := by
            refine ⟨hAdv.1, Or.inl ?_⟩
            refine ⟨hFileDiff0, ?_⟩
            have hDirNe : Movement.pawnDirection p.color ≠ 0 := pawnDirection_ne_zero p.color
            have : Movement.rankDiff src tgt = -2 * Movement.pawnDirection p.color := by simpa using hRd2
            intro h0
            have : Movement.pawnDirection p.color = 0 := by omega
            exact hDirNe this

          -- Get the intermediate square and show it is empty via `pathClear`.
          have hOff2 : Movement.rookOffset src tgt = 2 := by
            have hFdAbs : (Movement.fileDiff src tgt).natAbs = 0 := by
              simp [hFileDiff0]
            have hRdAbs : (Movement.rankDiff src tgt).natAbs = 2 := by
              have hRd : Movement.rankDiff src tgt = -2 * Movement.pawnDirection p.color := by
                simpa using hRd2
              cases hC : p.color with
              | White =>
                  have hRd' : Movement.rankDiff src tgt = -2 := by
                    simpa [Movement.pawnDirection, hC] using hRd
                  simp [hRd']
              | Black =>
                  have hRd' : Movement.rankDiff src tgt = 2 := by
                    simpa [Movement.pawnDirection, hC] using hRd
                  simp [hRd']
            simp [Movement.rookOffset, hFdAbs, hRdAbs]
          have hMidEx :
              ∃ mid,
                squareFromInts (src.fileInt + (Movement.rookDelta src tgt).1 * (1 : Int))
                    (src.rankInt + (Movement.rookDelta src tgt).2 * (1 : Int)) =
                  some mid := by
            have : (1 : Nat) ≤ Movement.rookOffset src tgt := by simp [hOff2]
            simpa using Chess.Movement.squareFromInts_rookDelta_step_some src tgt hRook 1 this
          rcases hMidEx with ⟨mid, hMid⟩
          have hMidMem :
              mid ∈ squaresBetween src tgt :=
            Chess.Movement.rook_step_square_mem_squaresBetween src tgt hRook 1 (by decide) (by
              -- 1 < rookOffset = 2
              simp [hOff2]) mid (by simpa using hMid)
          have hBetweenEmpty :
              ∀ sq, sq ∈ squaresBetween src tgt → board sq = none :=
            (pathClear_eq_true_iff board src tgt).1 hPC
          have hMidEmpty : isEmpty board mid = true := by
            have : board mid = none := hBetweenEmpty mid hMidMem
            simpa [isEmpty] using this

          -- Show `twoStep = some tgt` by the rook offset lemma.
          have hTwo :
              squareFromInts src.fileInt (src.rankInt + 2 * dir) = some tgt := by
            have hRankEq : tgt.rankInt = src.rankInt + 2 * dir := by
              have : Movement.rankDiff src tgt = -2 * dir := by
                -- `hRd2` already uses pawnDirection, rewrite to `dir`.
                simpa [dir] using hRd2
              unfold Movement.rankDiff at this
              omega
            have hFileEq : tgt.fileInt = src.fileInt := by
              unfold Movement.fileDiff at hFileDiff0
              omega
            have hSqCoords : squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
              Movement.squareFromInts_of_coords tgt
            simpa [hFileEq, hRankEq] using hSqCoords
          -- Relate `mid` with the generator's `oneStep`.
          have hOne : squareFromInts src.fileInt (src.rankInt + dir) = some mid := by
            have hDelta : Movement.rookDelta src tgt = (0, dir) := by
              have hRd2' : Movement.rankDiff src tgt = -2 * dir := by
                simpa [dir, color] using hRd2
              have hNeg : -Movement.rankDiff src tgt = 2 * dir := by
                omega
              unfold Movement.rookDelta
              -- fileDiff = 0, so only the rank step matters.
              have : Movement.fileDiff src tgt = 0 := hFileDiff0
              simp [this]
              -- Reduce the rank-step sign to the pawn direction.
              have hSign : Movement.signInt (2 * dir) = dir := by
                cases hC : color with
                | White =>
                    have h2 : Movement.signInt (2 : Int) = 1 := by
                      simpa using (Movement.signInt_ofNat_pos 2 (by decide))
                    simpa [dir, Movement.pawnDirection, hC] using h2
                | Black =>
                    have h2 : Movement.signInt (-(2 : Int)) = -1 := by
                      simpa using (Movement.signInt_neg_ofNat_pos 2 (by decide))
                    simpa [dir, Movement.pawnDirection, hC] using h2
              simpa [hNeg] using hSign
            have hMid' :
                squareFromInts (src.fileInt + (Movement.rookDelta src tgt).1)
                    (src.rankInt + (Movement.rookDelta src tgt).2) =
                  some mid := by
              simpa using hMid
            -- Rewrite `rookDelta` and simplify arithmetic.
            simpa [hDelta] using hMid'

          let base1 : Move := { piece := p, fromSq := src, toSq := mid }
          let base2 : Move := { piece := p, fromSq := src, toSq := tgt }
          have hBase2InForward :
              base2 ∈
                match squareFromInts src.fileInt (src.rankInt + dir) with
                | some target =>
                if isEmpty board target then
                  [({ piece := p, fromSq := src, toSq := target } : Move)] ++
                    (if src.rankNat = pawnStartRank p.color then
                        match squareFromInts src.fileInt (src.rankInt + 2 * dir) with
                        | some target2 =>
                            if isEmpty board target2 then
                              [({ piece := p, fromSq := src, toSq := target2 } : Move)]
                            else []
                        | none => []
                      else [])
                else []
                | none => [] := by
            simp [base2, hOne, hMidEmpty, hStart, hTwo, hEmptyTgt]

          have hMemProm : m ∈ promotionMoves base2 := by
            -- Same promotion reasoning as one-step.
            cases hProm : m.promotion with
            | none =>
                by_cases hRank : tgt.rankNat = pawnPromotionRank p.color
                ·
                  have : m.promotion.isSome := hPromoFwd ⟨by simpa [p] using hPawn, by simpa [tgt, p] using hRank⟩
                  cases (show False by simpa [hProm] using this)
                ·
                  have hEqMove :
                      ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := false } : Move) = m :=
                    move_eq_pawn_record m false (by simp [hCapFalse]) (by simp [hProm]) hNoCastle
                      hRookNone.1 hRookNone.2 (by
                        -- quiet move cannot be en passant by capture spec
                        have : ¬m.isEnPassant := by
                          intro hEP
                          have : m.isCapture = true := (hCapSpec).2 (Or.inr (by simpa using hEP))
                          cases (show False by simpa [hCapFalse] using this)
                        cases hE : m.isEnPassant with
                        | false => rfl
                        | true => cases this (by simp [hE]))
                  have hBaseEq : m = base2 := by
                    have : base2 = m := by simpa [base2, src, tgt, p] using hEqMove
                    exact this.symm
                  have hPawnBase2 : base2.piece.pieceType = PieceType.Pawn := by
                    simpa [base2, p] using hPawn
                  rw [hBaseEq]
                  have hNotPromo :
                      ¬(base2.piece.pieceType = PieceType.Pawn ∧
                        base2.toSq.rankNat = pawnPromotionRank base2.piece.color) := by
                    intro h
                    have : tgt.rankNat = pawnPromotionRank p.color := by
                      simpa [base2, tgt, p] using h.2
                    exact hRank this
                  have hPM : promotionMoves base2 = [base2] := by
                    simp [promotionMoves, hNotPromo]
                  simp [hPM]
            | some pt =>
                have hSome : m.promotion.isSome := by simp [hProm]
                have hRank : tgt.rankNat = pawnPromotionRank p.color := (hPromoBack hSome).2.1
                have hPtMem : pt ∈ promotionTargets := (hPromoBack hSome).2.2 pt (by simp [hProm])
                have hEqMove :
                    ({ base2 with promotion := some pt } : Move) = m := by
                  apply Move.ext <;> simp [base2, src, tgt, p, hProm, hCapFalse, hNoCastle, hRookNone.1, hRookNone.2, hEPFalse]
                have hPawnBase2 : base2.piece.pieceType = PieceType.Pawn := by
                  simpa [base2, p] using hPawn
                have hRankBase2 : base2.toSq.rankNat = pawnPromotionRank base2.piece.color := by
                  simpa [base2, tgt, p] using hRank
                simp [promotionMoves, hPawnBase2, hRankBase2, List.mem_map]
                exact ⟨pt, hPtMem, hEqMove⟩
          refine Or.inl ?_
          refine ⟨promotionMoves base2, ?_⟩
          refine ⟨?_, hMemProm⟩
          refine ⟨base2, ?_, rfl⟩
          exact hBase2InForward
  | true =>
      have hCapTrue : m.isCapture = true := by simpa using hCap
      cases hEP : m.isEnPassant with
      | false =>
          have hCapGeom :
              Movement.isPawnCapture p.color src tgt ∧ isEnemyAt board p.color tgt = true := by
            simpa [respectsGeometry, hPawn, hCapTrue, hEP, src, tgt, p, board] using hGeom
          have hEnemy : isEnemyAt board p.color tgt = true := hCapGeom.2
          have hEnemyNK : isEnemyNonKingAt board p.color tgt = true := by
            -- Combine the semantic destination constraint (no friendly piece and no king capture)
            -- with the fact that this is a non-EP capture.
            unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
            cases hAtTgt : board tgt with
            | none =>
                -- Contradiction: `isEnemyAt` cannot be true on an empty square.
                have : isEnemyAt board p.color tgt = false := by
                  simp [isEnemyAt, hAtTgt]
                cases (show False by simpa [this] using hEnemy)
            | some q =>
                have hAtTgt' : gs.board.get m.toSq = some q := by
                  -- `Board` coerces to `Square → Option Piece` via `Board.get`.
                  simpa [board, tgt] using hAtTgt
                have hNe : q.color ≠ p.color := by
                  have : decide (q.color ≠ p.color) = true := by
                    simpa [isEnemyAt, hAtTgt] using hEnemy
                  simpa [decide_eq_true_eq] using this
                have hNoKing : q.pieceType ≠ PieceType.King := by
                  have hBool :
                      (!decide (q.color = p.color) && !decide (q.pieceType = PieceType.King)) = true := by
                    simpa [hAtTgt'] using hDest
                  have hParts :
                      !decide (q.color = p.color) = true ∧ !decide (q.pieceType = PieceType.King) = true := by
                    simpa [Bool.and_eq_true] using hBool
                  have hDecFalse : decide (q.pieceType = PieceType.King) = false := by
                    simpa using hParts.2
                  exact of_decide_eq_false hDecFalse
                simp [isEnemyNonKingAt, hAtTgt, hNe, hNoKing]
          have hRankDiff : Movement.rankDiff src tgt = -dir := by
            have : Movement.rankDiff src tgt = -Movement.pawnDirection p.color := hCapGeom.1.2.2
            simpa [dir] using this
          have hTgtRank : tgt.rankInt = src.rankInt + dir := by
            unfold Movement.rankDiff at hRankDiff
            omega

          have hFdAbs : absInt (Movement.fileDiff src tgt) = 1 := hCapGeom.1.2.1
          have hDfCases : Movement.fileDiff src tgt = 1 ∨ Movement.fileDiff src tgt = -1 := by
            unfold absInt at hFdAbs
            by_cases hNonneg : 0 ≤ Movement.fileDiff src tgt
            · left
              have : Movement.fileDiff src tgt = 1 := by omega
              exact this
            · right
              have : -Movement.fileDiff src tgt = 1 := by
                simpa [hNonneg] using hFdAbs
              omega

          -- Determine the generator df (±1) and show the target square is at that offset.
          have hSq :
              (∃ df : Int,
                  (df = -1 ∨ df = 1) ∧
                    squareFromInts (src.fileInt + df) (src.rankInt + dir) = some tgt) := by
            cases hDfCases with
            | inl hFd1 =>
                have hTgtFile : tgt.fileInt = src.fileInt + (-1) := by
                  unfold Movement.fileDiff at hFd1
                  omega
                have hSqCoords : squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
                  squareFromInts_of_coords tgt
                have : squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) = some tgt := by
                  simpa [hTgtFile, hTgtRank] using hSqCoords
                exact ⟨-1, Or.inl rfl, this⟩
            | inr hFdNeg =>
                have hTgtFile : tgt.fileInt = src.fileInt + (1 : Int) := by
                  unfold Movement.fileDiff at hFdNeg
                  omega
                have hSqCoords : squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
                  squareFromInts_of_coords tgt
                have : squareFromInts (src.fileInt + (1 : Int)) (src.rankInt + dir) = some tgt := by
                  simpa [hTgtFile, hTgtRank] using hSqCoords
                exact ⟨1, Or.inr rfl, this⟩

          rcases hSq with ⟨df, hDfMem, hSqTgt⟩
          let base : Move := { piece := p, fromSq := src, toSq := tgt, isCapture := true }

          have hMemProm : m ∈ promotionMoves base := by
            cases hProm : m.promotion with
            | none =>
                by_cases hRank : tgt.rankNat = pawnPromotionRank p.color
                ·
                  have : m.promotion.isSome := hPromoFwd ⟨by simpa [p] using hPawn, by simpa [tgt, p] using hRank⟩
                  cases (show False by simpa [hProm] using this)
                ·
                  have hEqMove :
                      ({ piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true } : Move) = m :=
                    move_eq_pawn_record m true (by simp [hCapTrue]) (by simp [hProm]) hNoCastle
                      hRookNone.1 hRookNone.2 (by simp [hEP] )
                  have hBaseEq : m = base := by
                    have : base = m := by simpa [base, src, tgt, p] using hEqMove
                    exact this.symm
                  have hPawnBase : base.piece.pieceType = PieceType.Pawn := by
                    simpa [base, p] using hPawn
                  rw [hBaseEq]
                  have hNotPromo :
                      ¬(base.piece.pieceType = PieceType.Pawn ∧
                        base.toSq.rankNat = pawnPromotionRank base.piece.color) := by
                    intro h
                    have : tgt.rankNat = pawnPromotionRank p.color := by
                      simpa [base, tgt, p] using h.2
                    exact hRank this
                  have hPM : promotionMoves base = [base] := by
                    simp [promotionMoves, hNotPromo]
                  simp [hPM]
            | some pt =>
                have hSome : m.promotion.isSome := by simp [hProm]
                have hRank : tgt.rankNat = pawnPromotionRank p.color := (hPromoBack hSome).2.1
                have hPtMem : pt ∈ promotionTargets := (hPromoBack hSome).2.2 pt (by simp [hProm])
                have hEqMove :
                    ({ base with promotion := some pt } : Move) = m := by
                  apply Move.ext <;> simp [base, src, tgt, p, hProm, hCapTrue, hNoCastle, hRookNone.1, hRookNone.2, hEP]
                have hPawnBase : base.piece.pieceType = PieceType.Pawn := by
                  simpa [base, p] using hPawn
                have hRankBase : base.toSq.rankNat = pawnPromotionRank base.piece.color := by
                  simpa [base, tgt, p] using hRank
                simp [promotionMoves, hPawnBase, hRankBase, List.mem_map]
                exact ⟨pt, hPtMem, hEqMove⟩

          -- Show membership in the `captureMoves` fold (either df = -1 or df = 1).
          have hCaptureMem :
              m ∈
                ([-1, 1] : List Int).foldr
                    (fun df0 acc =>
                      match squareFromInts (src.fileInt + df0) (src.rankInt + dir) with
                      | some target =>
                          if isEnemyNonKingAt board p.color target then
                            promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
                          else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
                            { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
                          else
                            acc
                      | none => acc)
                    [] := by
            cases hDfMem with
            | inl hDf =>
                subst hDf
                -- df = -1, so the head stepFn appends `promotionMoves base`.
                simp [List.foldr, hSqTgt, hEnemyNK, base]
                exact Or.inl hMemProm
            | inr hDf =>
                subst hDf
                -- df = 1, so it appears in the tail accumulator.
                simp [List.foldr, hSqTgt, hEnemyNK, base]
                cases hSq : squareFromInts (src.fileInt + -1) (src.rankInt + dir) with
                | none =>
                    simpa [hSq] using hMemProm
                | some target =>
                    cases hEnemy2 : isEnemyNonKingAt board p.color target with
                    | true =>
                        have :
                            m ∈
                              promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++
                                promotionMoves base :=
                          List.mem_append.2 (Or.inr hMemProm)
                        simpa [hSq, hEnemy2] using this
                    | false =>
                        by_cases hEP2 :
                            gs.enPassantTarget = some target ∧
                              isEmpty board target ∧
                              enPassantFromHistory gs target = true
                        ·
                          have :
                              m ∈
                                ({ piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :
                                    Move) ::
                                  promotionMoves base :=
                            List.mem_cons_of_mem _ hMemProm
                          simpa [hSq, hEnemy2, hEP2] using this
                        ·
                          simpa [hSq, hEnemy2, hEP2] using hMemProm
          exact Or.inr (by simpa using hCaptureMem)
      | true =>
          have hEPGeom :
              Movement.isPawnCapture p.color src tgt ∧
                gs.enPassantTarget = some tgt ∧
                isEmpty board tgt = true ∧
                enPassantFromHistory gs tgt = true := by
            simpa [respectsGeometry, hPawn, hCapTrue, hEP, src, tgt, p, board] using hGeom
          have hRankEP : tgt.rankNat = 2 ∨ tgt.rankNat = 5 := by
            simpa [hasValidEPRank, hEPGeom.2.1, tgt] using hValid
          have hNotPromo : tgt.rankNat ≠ pawnPromotionRank p.color :=
            validEPRank_not_promotion tgt p.color hRankEP
          have hPromNone : m.promotion = none := by
            cases hProm : m.promotion with
            | none => rfl
            | some pt =>
                have hSome : m.promotion.isSome := by simp [hProm]
                have hRank : tgt.rankNat = pawnPromotionRank p.color := (hPromoBack hSome).2.1
                have : False := hNotPromo (by simpa [tgt, p] using hRank)
                cases this
          -- Determine the generator df (±1) and show the EP move is exactly the one consed.
          have hFdAbs : absInt (Movement.fileDiff src tgt) = 1 := hEPGeom.1.2.1
          have hDfCases : Movement.fileDiff src tgt = 1 ∨ Movement.fileDiff src tgt = -1 := by
            unfold absInt at hFdAbs
            by_cases hNonneg : 0 ≤ Movement.fileDiff src tgt
            · left
              have : Movement.fileDiff src tgt = 1 := by omega
              exact this
            · right
              have : -Movement.fileDiff src tgt = 1 := by
                simpa [hNonneg] using hFdAbs
              omega
          have hRankDiff : Movement.rankDiff src tgt = -dir := by
            have : Movement.rankDiff src tgt = -Movement.pawnDirection p.color := hEPGeom.1.2.2
            simpa [dir] using this
          have hTgtRank : tgt.rankInt = src.rankInt + dir := by
            unfold Movement.rankDiff at hRankDiff
            omega
          have hSqTgt :
              ∃ df : Int, (df = -1 ∨ df = 1) ∧ squareFromInts (src.fileInt + df) (src.rankInt + dir) = some tgt := by
            cases hDfCases with
            | inl hFd1 =>
                have hTgtFile : tgt.fileInt = src.fileInt + (-1) := by
                  unfold Movement.fileDiff at hFd1
                  omega
                have hSqCoords : squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
                  squareFromInts_of_coords tgt
                have : squareFromInts (src.fileInt + (-1)) (src.rankInt + dir) = some tgt := by
                  simpa [hTgtFile, hTgtRank] using hSqCoords
                exact ⟨-1, Or.inl rfl, this⟩
            | inr hFdNeg =>
                have hTgtFile : tgt.fileInt = src.fileInt + (1 : Int) := by
                  unfold Movement.fileDiff at hFdNeg
                  omega
                have hSqCoords : squareFromInts tgt.fileInt tgt.rankInt = some tgt :=
                  squareFromInts_of_coords tgt
                have : squareFromInts (src.fileInt + (1 : Int)) (src.rankInt + dir) = some tgt := by
                  simpa [hTgtFile, hTgtRank] using hSqCoords
                exact ⟨1, Or.inr rfl, this⟩
          rcases hSqTgt with ⟨df, hDfMem, hSqTgt⟩
          have hEPCond :
              gs.enPassantTarget = some tgt ∧
                isEmpty board tgt = true ∧
                enPassantFromHistory gs tgt = true := hEPGeom.2
          have hEqMove :
              ({ piece := p, fromSq := src, toSq := tgt, isCapture := true, isEnPassant := true } : Move) = m := by
            apply Move.ext <;> simp [src, tgt, p, hCapTrue, hPromNone, hNoCastle, hRookNone.1, hRookNone.2, hEP]
          have hEnemyFalse : isEnemyNonKingAt board p.color tgt = false := by
            have : board tgt = none := by
              simpa [isEmpty] using hEPGeom.2.2.1
            simp [isEnemyNonKingAt, this]
          have hCaptureMem :
              m ∈
                ([-1, 1] : List Int).foldr
                    (fun df0 acc =>
                      match squareFromInts (src.fileInt + df0) (src.rankInt + dir) with
                      | some target =>
                          if isEnemyNonKingAt board p.color target then
                            promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
                          else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
                            { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
                          else
                            acc
                      | none => acc)
                    [] := by
            let stepFn : Int → List Move → List Move :=
              fun df0 acc =>
                match squareFromInts (src.fileInt + df0) (src.rankInt + dir) with
                | some target =>
                    if isEnemyNonKingAt board p.color target then
                      promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc
                    else if gs.enPassantTarget = some target ∧ isEmpty board target ∧ enPassantFromHistory gs target = true then
                      { piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } :: acc
                    else
                      acc
                | none => acc
            have hPreserve :
                ∀ df0 acc, m ∈ acc → m ∈ stepFn df0 acc := by
              intro df0 acc hMem
              unfold stepFn
              cases hSq : squareFromInts (src.fileInt + df0) (src.rankInt + dir) with
              | none =>
                  simpa [hSq] using hMem
              | some target =>
                  cases hEnemy : isEnemyNonKingAt board p.color target with
                  | true =>
                      -- appended lists preserve accumulator membership
                      have : m ∈ promotionMoves { piece := p, fromSq := src, toSq := target, isCapture := true } ++ acc :=
                        List.mem_append.2 (Or.inr hMem)
                      simpa [hSq, hEnemy] using this
                  | false =>
                      by_cases hEP' :
                          gs.enPassantTarget = some target ∧
                            isEmpty board target ∧
                            enPassantFromHistory gs target = true
                      ·
                        have : m ∈ ({ piece := p, fromSq := src, toSq := target, isCapture := true, isEnPassant := true } : Move) :: acc :=
                          List.mem_cons_of_mem _ hMem
                        simpa [hSq, hEnemy, hEP'] using this
                      ·
                        simpa [hSq, hEnemy, hEP'] using hMem
            cases hDfMem with
            | inl hDf =>
                -- df = -1: the head step inserts our EP move directly.
                subst hDf
                -- foldr over [-1, 1] is `stepFn (-1) (stepFn 1 [])`
                have : m ∈ stepFn (-1) (stepFn 1 []) := by
                  -- Use the target equation to select the EP branch.
                  simp [stepFn, hSqTgt, hEnemyFalse, hEPCond, hEqMove]
                simpa [List.foldr, stepFn] using this
            | inr hDf =>
                -- df = 1: show membership in the tail, then preserve through the head step.
                subst hDf
                have hTail : m ∈ stepFn 1 [] := by
                  simp [stepFn, hSqTgt, hEnemyFalse, hEPCond, hEqMove]
                have : m ∈ stepFn (-1) (stepFn 1 []) :=
                  hPreserve (-1) (stepFn 1 []) hTail
                simpa [List.foldr, stepFn] using this
          exact Or.inr (by simpa using hCaptureMem)

end Rules
end Chess
