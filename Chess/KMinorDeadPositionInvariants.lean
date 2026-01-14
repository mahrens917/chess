import Chess.KMinorPreservationLemmas
import Chess.KkDeadPositionProofs
import Chess.RulesComplete

namespace Chess
namespace Rules

/-!
Invariants used for semantic K+minor dead-position proofs.

This module focuses on **closure** under `applyLegalMove(s)`; the actual “no checkmate possible”
argument (needed to derive `Rules.isDeadPosition`) is handled separately.
-/

def KMinorInv (gs : GameState) : Prop :=
  ∃ wk bk msq mp,
    KingsPlusMinor gs.board wk bk msq mp ∧
      ¬ Movement.isKingStep wk bk

def KMinorOrKkInv (gs : GameState) : Prop :=
  KMinorInv gs ∨ KkInv gs

private theorem mem_allLegalMoves_implies_turnMatches
    (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs → turnMatches gs m = true := by
  intro hMem
  have hBasic : basicMoveLegalBool gs m = true :=
    mem_allLegalMoves_implies_basicMoveLegalBool gs m hMem
  have hConj :
      (((originHasPiece gs m = true ∧ turnMatches gs m = true) ∧
            destinationFriendlyFree gs m = true) ∧
          captureFlagConsistent gs m = true) ∧
        squaresDiffer m = true := by
    simpa [basicMoveLegalBool, Bool.and_eq_true] using hBasic
  exact hConj.1.1.1.2

theorem KMinorInv.to_KMinorOrKkInv (gs : GameState) : KMinorInv gs → KMinorOrKkInv gs := by
  intro h
  exact Or.inl h

theorem KkInv.to_KMinorOrKkInv (gs : GameState) : KkInv gs → KMinorOrKkInv gs := by
  intro h
  exact Or.inr h

theorem KMinorInv.applyLegalMove_preserved_or_kkInv
    (gs : GameState) (m : Move) (gs' : GameState) :
    KMinorInv gs →
    applyLegalMove gs m = Except.ok gs' →
    KMinorOrKkInv gs' := by
  intro hInv hOk
  rcases hInv with ⟨wk, bk, msq, mp, hKPM, hNoAdj⟩

  -- Unpack `applyLegalMove`.
  have hOk' := hOk
  unfold applyLegalMove at hOk'
  cases hOpt : applyLegalMove? gs m with
  | none =>
      simp [hOpt] at hOk'
  | some nxt =>
      have hnxt : nxt = gs' := by
        have : (Except.ok nxt : Except String GameState) = Except.ok gs' := by
          simpa [hOpt] using hOk'
        exact Except.ok.inj this

      have hIsLegal : isLegalMove gs m = true := by
        unfold applyLegalMove? at hOpt
        by_cases h : isLegalMove gs m = true
        · exact h
        · simp [h] at hOpt

      have hPlay : nxt = GameState.playMove gs m := by
        unfold applyLegalMove? at hOpt
        simp [hIsLegal] at hOpt
        exact hOpt.symm

      have hMem : m ∈ allLegalMoves gs := by
        unfold isLegalMove at hIsLegal
        rcases (List.any_eq_true).1 hIsLegal with ⟨cand, hCandMem, hCandEq⟩
        have hEq : cand = m := by simpa using hCandEq
        simpa [hEq] using hCandMem

      have hEnc : encodedLegal gs m :=
        (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
      rcases hEnc with ⟨src, p, hAtSrc, hTurn, _hTargets, _hPin, hSafe⟩

      have hBoardEq : gs'.board = (gs.movePiece m).board := by
        have hEq1 : gs'.board = nxt.board := (congrArg GameState.board hnxt).symm
        have hEq2 : nxt.board = (gs.movePiece m).board := by
          have hEqPlay : nxt.board = (GameState.playMove gs m).board :=
            congrArg GameState.board hPlay
          exact hEqPlay.trans (GameState.playMove_board gs m)
        exact hEq1.trans hEq2

      have hNotCheck : inCheck (gs.movePiece m).board gs.toMove = false := by
        unfold basicLegalAndSafe at hSafe
        have : basicMoveLegalBool gs m = true ∧
            !(inCheck (gs.movePiece m).board gs.toMove) = true := by
          simpa [Bool.and_eq_true] using hSafe
        have hNot : !(inCheck (gs.movePiece m).board gs.toMove) = true := this.2
        simpa using hNot

      have hTurnM : m.piece.color = gs.toMove := by
        have hTurnB : turnMatches gs m = true :=
          mem_allLegalMoves_implies_turnMatches gs m hMem
        unfold turnMatches at hTurnB
        exact of_decide_eq_true hTurnB

      -- Decide capture vs non-capture.
      cases hCap : m.isCapture with
      | false =>
          have hPres :=
            KingsPlusMinor.mem_allLegalMoves_isCapture_false_preserves
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem hCap
          rcases hPres with ⟨hPiece, hKPM'⟩ | ⟨hPiece, hKPM'⟩ | ⟨hPiece, hKPM'⟩
          · -- white king moved: new king square is `m.toSq`
            have hKPMnxt' : KingsPlusMinor gs'.board m.toSq bk msq mp := by
              simpa [hBoardEq] using hKPM'
            have hToMove : gs.toMove = Color.White := by
              have : Color.White = gs.toMove := by
                simpa [hPiece, kingPiece] using hTurnM
              exact this.symm
            have hNotCheckW : inCheck (gs.movePiece m).board Color.White = false := by
              simpa [hToMove] using hNotCheck
            have hNoAdj' : ¬ Movement.isKingStep m.toSq bk := by
              intro hStep
              have hChk : inCheck (gs.movePiece m).board Color.White = true :=
                KingsPlusMinor.inCheck_white_of_isKingStep (h := hKPM') (Movement.isKingStep_symm _ _ hStep)
              have : (true : Bool) = false := by
                simpa [hChk] using hNotCheckW
              cases this
            refine Or.inl ?_
            exact ⟨m.toSq, bk, msq, mp, hKPMnxt', hNoAdj'⟩
          · -- black king moved
            have hKPMnxt' : KingsPlusMinor gs'.board wk m.toSq msq mp := by
              simpa [hBoardEq] using hKPM'
            have hToMove : gs.toMove = Color.Black := by
              have : Color.Black = gs.toMove := by
                simpa [hPiece, kingPiece] using hTurnM
              exact this.symm
            have hNotCheckB : inCheck (gs.movePiece m).board Color.Black = false := by
              simpa [hToMove] using hNotCheck
            have hNoAdj' : ¬ Movement.isKingStep wk m.toSq := by
              intro hStep
              have hChk : inCheck (gs.movePiece m).board Color.Black = true :=
                KingsPlusMinor.inCheck_black_of_isKingStep (h := hKPM') hStep
              have : (true : Bool) = false := by
                simpa [hChk] using hNotCheckB
              cases this
            refine Or.inl ?_
            exact ⟨wk, m.toSq, msq, mp, hKPMnxt', hNoAdj'⟩
          · -- minor moved; kings unchanged, so keep original non-adjacent.
            refine Or.inl ?_
            have hKPMnxt' : KingsPlusMinor gs'.board wk bk m.toSq mp := by
              simpa [hBoardEq] using hKPM'
            exact ⟨wk, bk, m.toSq, mp, hKPMnxt', hNoAdj⟩
      | true =>
          -- Capture: on a KingsPlusMinor board, captures can only be “opponent king captures the minor”.
          have hTo :
              m.toSq = msq :=
            KingsPlusMinor.mem_allLegalMoves_isCapture_implies_toSq_minorSquare
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
          have hMover :
              m.piece = kingPiece mp.color.opposite :=
            KingsPlusMinor.mem_allLegalMoves_isCapture_implies_piece_is_opponentKing
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
          have hFrom :
              m.fromSq = (if mp.color = Color.White then bk else wk) :=
            KingsPlusMinor.mem_allLegalMoves_isCapture_implies_fromSq_opponentKingSquare
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)

          -- Split by which king is moving (determined by `mp.color`).
          cases hC : mp.color with
          | White =>
              have hPiece : m.piece = kingPiece Color.Black := by
                simpa [hC, Color.opposite] using hMover
              have hFrom' : m.fromSq = bk := by simpa [hC] using hFrom
              have hKO : KingsOnly (gs.movePiece m).board wk msq := by
                -- black king captures the white minor
                have hTo' : m.toSq = msq := hTo
                exact
                  KingsPlusMinor.blackKing_captureMinor_yields_kingsOnly
                    (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
                    hKPM hMem hPiece hFrom' hTo'
              have hKOnxt : KingsOnly gs'.board wk msq := by
                simpa [hBoardEq] using hKO
              have hToMove : gs.toMove = Color.Black := by
                have : Color.Black = gs.toMove := by
                  simpa [hPiece, kingPiece] using hTurnM
                exact this.symm
              have hNotCheckB : inCheck (gs.movePiece m).board Color.Black = false := by
                simpa [hToMove] using hNotCheck
              have hNoAdj' : ¬ Movement.isKingStep wk msq := by
                intro hStep
                have hChk : inCheck (gs.movePiece m).board Color.Black = true :=
                  (KingsOnly.inCheck_black_eq_true_iff_isKingStep hKO).2 hStep
                have : (true : Bool) = false := by
                  simpa [hChk] using hNotCheckB
                cases this
              refine Or.inr ?_
              exact ⟨wk, msq, hKOnxt, hNoAdj'⟩
          | Black =>
              have hPiece : m.piece = kingPiece Color.White := by
                simpa [hC, Color.opposite] using hMover
              have hFrom' : m.fromSq = wk := by simpa [hC] using hFrom
              have hKO : KingsOnly (gs.movePiece m).board msq bk := by
                have hTo' : m.toSq = msq := hTo
                exact
                  KingsPlusMinor.whiteKing_captureMinor_yields_kingsOnly
                    (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
                    hKPM hMem hPiece hFrom' hTo'
              have hKOnxt : KingsOnly gs'.board msq bk := by
                simpa [hBoardEq] using hKO
              have hToMove : gs.toMove = Color.White := by
                have : Color.White = gs.toMove := by
                  simpa [hPiece, kingPiece] using hTurnM
                exact this.symm
              have hNotCheckW : inCheck (gs.movePiece m).board Color.White = false := by
                simpa [hToMove] using hNotCheck
              have hNoAdj' : ¬ Movement.isKingStep msq bk := by
                intro hStep
                have hChk : inCheck (gs.movePiece m).board Color.White = true :=
                  (KingsOnly.inCheck_white_eq_true_iff_isKingStep hKO).2 (Movement.isKingStep_symm _ _ hStep)
                have : (true : Bool) = false := by
                  simpa [hChk] using hNotCheckW
                cases this
              refine Or.inr ?_
              exact ⟨msq, bk, hKOnxt, hNoAdj'⟩

theorem KMinorOrKkInv.applyLegalMove_preserved
    (gs : GameState) (m : Move) (gs' : GameState) :
    KMinorOrKkInv gs →
    applyLegalMove gs m = Except.ok gs' →
    KMinorOrKkInv gs' := by
  intro hInv hOk
  rcases hInv with hKMinor | hKk
  · exact KMinorInv.applyLegalMove_preserved_or_kkInv gs m gs' hKMinor hOk
  · exact Or.inr (KkInv.applyLegalMove_preserved gs m gs' hKk hOk)

theorem KMinorOrKkInv.applyLegalMoves_preserved
    (gs : GameState) (moves : List Move) (gs' : GameState) :
    KMinorOrKkInv gs →
    applyLegalMoves gs moves = Except.ok gs' →
    KMinorOrKkInv gs' := by
  intro hInv hOk
  induction moves generalizing gs with
  | nil =>
      have hEq : gs' = gs := by
        have : (Except.ok gs : Except String GameState) = Except.ok gs' := by
          simpa [applyLegalMoves_nil] using hOk
        injection this with hEq'
        exact hEq'.symm
      subst hEq
      exact hInv
  | cons m ms ih =>
      rcases (applyLegalMoves_eq_ok_cons_iff gs m ms gs').1 hOk with ⟨gs1, hOk1, hOk2⟩
      have hInv1 : KMinorOrKkInv gs1 :=
        KMinorOrKkInv.applyLegalMove_preserved gs m gs1 hInv hOk1
      exact ih gs1 hInv1 hOk2

end Rules
end Chess
