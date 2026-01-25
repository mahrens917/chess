import Chess.ApplyLegalMovesLemmas
import Chess.KkBoard
import Chess.Movement
import Chess.RulesComplete

namespace Chess
namespace Rules

def KkInv (gs : GameState) : Prop :=
  ∃ wk bk, KingsOnly gs.board wk bk ∧ ¬ Movement.isKingStep wk bk

theorem finalizeResult_board (before after : GameState) :
    (finalizeResult before after).board = after.board := by
  unfold finalizeResult
  by_cases hRes : after.result.isSome = true
  · simp [hRes]
  · simp [hRes]
    by_cases hMate : isCheckmate after = true
    · simp [hMate]
    · simp [hMate]
      let pDraw : Prop :=
        ((isStalemate after = true ∨ isSeventyFiveMoveDraw after = true) ∨ fivefoldRepetition after = true) ∨
          deadPosition after = true
      by_cases hP : pDraw <;> simp [pDraw, hP]

theorem GameState.playMove_board (gs : GameState) (m : Move) :
    (GameState.playMove gs m).board = (gs.movePiece m).board := by
  unfold GameState.playMove
  simp [finalizeResult_board]

theorem kkInv_kkGameState (wk bk : Square) (toMove : Color)
    (hNe : wk ≠ bk)
    (hNoAdj : ¬ Movement.isKingStep wk bk) :
    KkInv (kkGameState wk bk toMove) := by
  refine ⟨wk, bk, ?_, hNoAdj⟩
  simpa [kkGameState] using kingsOnly_kkBoard wk bk hNe

theorem KkInv.inCheckStatus_false (gs : GameState) :
    KkInv gs → inCheckStatus gs = false := by
  rintro ⟨wk, bk, hKO, hNoAdj⟩
  cases hTurn : gs.toMove with
  | White =>
      have hNoAdj' : ¬ Movement.isKingStep bk wk := by
        intro hStep
        exact hNoAdj (Movement.isKingStep_symm bk wk hStep)
      cases hStatus : inCheckStatus gs with
      | true =>
          have : Movement.isKingStep bk wk :=
            (KingsOnly.inCheck_white_eq_true_iff_isKingStep hKO).1 (by
              simpa [inCheckStatus, hTurn] using hStatus)
          exact (hNoAdj' this).elim
      | false =>
          rfl
  | Black =>
      cases hStatus : inCheckStatus gs with
      | true =>
          have : Movement.isKingStep wk bk :=
            (KingsOnly.inCheck_black_eq_true_iff_isKingStep hKO).1 (by
              simpa [inCheckStatus, hTurn] using hStatus)
          exact (hNoAdj this).elim
      | false =>
          rfl

theorem KkInv.isCheckmate_false (gs : GameState) :
    KkInv gs → isCheckmate gs = false := by
  intro hInv
  have hChk : inCheckStatus gs = false :=
    KkInv.inCheckStatus_false gs hInv
  simp [isCheckmate, hChk]

theorem KkInv.applyLegalMove_preserved (gs : GameState) (m : Move) (gs' : GameState) :
    KkInv gs →
    applyLegalMove gs m = Except.ok gs' →
    KkInv gs' := by
  intro hInv hOk
  rcases hInv with ⟨wk, bk, hKO, hNoAdj⟩

  -- Unpack `applyLegalMove`.
  have hOk' := hOk
  unfold applyLegalMove at hOk'
  cases hOpt : applyLegalMove? gs m with
  | none =>
      simp [hOpt] at hOk'
  | some nxt =>
      have hnxt : nxt = gs' := by
        have : (Except.ok nxt : Except String GameState) = Except.ok gs' := by
          -- `simp` will reduce the match.
          simpa [hOpt] using hOk'
        exact Except.ok.inj this

      have hIsLegal : isLegalMove gs m = true := by
        -- `applyLegalMove?` can only be `some` when `isLegalMove` is true.
        unfold applyLegalMove? at hOpt
        by_cases h : isLegalMove gs m = true
        · exact h
        · simp [h] at hOpt

      have hPlay : nxt = GameState.playMove gs m := by
        unfold applyLegalMove? at hOpt
        simp [hIsLegal] at hOpt
        exact hOpt.symm

      -- Recover the generator witnesses for `m`.
      have hMem : m ∈ allLegalMoves gs := by
        unfold isLegalMove at hIsLegal
        rcases (List.any_eq_true).1 hIsLegal with ⟨cand, hCandMem, hCandEq⟩
        have hEq : cand = m := by
          simpa using hCandEq
        simpa [hEq] using hCandMem
      have hEnc : encodedLegal gs m :=
        (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
      rcases hEnc with ⟨src, p, hAtSrc, hTurn, hTargets, _hPin, hSafe⟩

      -- Identify the moving piece/square using `KingsOnly`.
      have hAtSrc' : gs.board.get src = some p := by simpa using hAtSrc
      cases hToMove : gs.toMove with
      | White =>
          have ⟨hSrcEq, hPEq⟩ :=
            KingsOnly.white_piece_of_get_of_color hKO src p hAtSrc' (by simpa [hToMove] using hTurn)
          cases hSrcEq
          subst hPEq
          -- `pieceTargets` for a kings-only board contains only standard king steps.
          have hNoCastleTrue : castleMoveIfLegal gs true = none :=
            KingsOnly.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKO true
          have hNoCastleFalse : castleMoveIfLegal gs false = none :=
            KingsOnly.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKO false
          have hStdMem :
              m ∈
                (Movement.kingTargets wk).filterMap (fun target =>
                  if destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := target } then
                    match gs.board target with
                    | some _ => some { piece := kingPiece Color.White, fromSq := wk, toSq := target, isCapture := true }
                    | none => some { piece := kingPiece Color.White, fromSq := wk, toSq := target }
                  else
                    none) := by
            -- Castling is impossible on a kings-only board.
            simpa [pieceTargets, kingPiece, hNoCastleTrue, hNoCastleFalse] using hTargets
          rcases List.mem_filterMap.1 hStdMem with ⟨target, hTarget, hSome⟩
          have hFrom : m.fromSq = wk := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hPiece : m.piece = kingPiece Color.White := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hNoCastle : m.isCastle = false := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hNoEP : m.isEnPassant = false := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hNoPromo : m.promotion = none := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hBasic : basicMoveLegalBool gs m = true :=
            basicLegalAndSafe_implies_basicMoveLegalBool gs m hSafe
          have hSquaresDiffer : squaresDiffer m = true := by
            have hb0 := hBasic
            unfold basicMoveLegalBool at hb0
            exact (Eq.mp (Bool.and_eq_true _ _) hb0).2
          have hSafeParts :
              basicMoveLegalBool gs m = true ∧ inCheck (gs.movePiece m).board gs.toMove = false := by
            have hs := hSafe
            unfold basicLegalAndSafe at hs
            simp at hs
            exact hs
          have hSafe' : inCheck (gs.movePiece m).board Color.White = false := by
            simpa [hToMove] using hSafeParts.2
          have hTo : m.toSq = target := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.White, fromSq := wk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          -- Destination is not the black king square (king step non-adjacency).
          have hToNeBk : m.toSq ≠ bk := by
            intro hEq
            have hTargetBk : target = bk := by rw [← hTo, hEq]
            have hStep : Movement.isKingStep wk bk :=
              hTargetBk ▸ (Movement.mem_kingTargets_iff wk target).mp hTarget
            exact hNoAdj hStep
          -- Compute the resulting board (no EP/castling/promotion are possible for king moves).
          have hMovedBoard :
              (gs.movePiece m).board =
                (gs.board.update wk none).update m.toSq (some (kingPiece Color.White)) := by
            -- Reduce `movePiece` using the flags discovered above.
            unfold GameState.movePiece
            simp [hFrom, hPiece, hNoEP, hNoCastle, hNoPromo, GameState.promotedPiece, kingPiece]
          have hBoard' : nxt.board =
              (gs.board.update wk none).update m.toSq (some (kingPiece Color.White)) := by
            have hNxtBoard : nxt.board = (gs.movePiece m).board := by
              calc
                nxt.board = (GameState.playMove gs m).board := by
                  simpa [hPlay] using congrArg GameState.board hPlay
                _ = (gs.movePiece m).board := by
                  simpa using GameState.playMove_board gs m
            simpa [hNxtBoard] using hMovedBoard
          -- Show the resulting board still contains only kings.
          have hKO' : KingsOnly nxt.board m.toSq bk := by
            constructor
            · -- white king at `m.toSq`
              simp [hBoard', Board.update_eq]
            constructor
            · -- black king at `bk`
              have hNe1 : bk ≠ wk := hKO.2.2.1.symm
              have hNe2 : bk ≠ m.toSq := by
                intro hEq
                exact hToNeBk hEq.symm
              simp [hBoard', Board.update_ne _ _ _ hNe2, Board.update_ne _ _ _ hNe1, hKO.2.1]
            constructor
            · exact hToNeBk
            · intro sq hNeW hNeB
              by_cases hSqWk : sq = wk
              · cases hSqWk
                have hNe : wk ≠ m.toSq := by
                  have hDiff : m.fromSq ≠ m.toSq := by
                    simpa [squaresDiffer] using hSquaresDiffer
                  intro hEq
                  apply hDiff
                  simp [hFrom, hEq]
                simp [hBoard', Board.update_ne _ _ _ hNe, Board.update_eq]
              · have hNeTo : sq ≠ m.toSq := by simpa using hNeW
                have hNeFrom : sq ≠ wk := hSqWk
                have hStart : gs.board.get sq = none := by
                  exact hKO.2.2.2 sq hNeFrom (by
                    intro hEq
                    subst hEq
                    exact hNeB rfl)
                simp [hBoard', Board.update_ne _ _ _ hNeTo, Board.update_ne _ _ _ hNeFrom, hStart]

          -- Use safety to show the kings are not adjacent after the move.
          have hNoAdj' : ¬ Movement.isKingStep m.toSq bk := by
            intro hStep
            have : Movement.isKingStep bk m.toSq :=
              Movement.isKingStep_symm _ _ hStep
            have : inCheck nxt.board Color.White = true :=
              (KingsOnly.inCheck_white_eq_true_iff_isKingStep hKO').2 this
            have hEqBoard : (gs.movePiece m).board = nxt.board :=
              Eq.trans hMovedBoard (hBoard'.symm)
            have : inCheck (gs.movePiece m).board Color.White = true := by
              simpa [hEqBoard] using this
            simp [hSafe'] at this
          have hInvNxt : KkInv nxt := ⟨m.toSq, bk, hKO', hNoAdj'⟩
          simpa [hnxt] using hInvNxt
      | Black =>
          have ⟨hSrcEq, hPEq⟩ :=
            KingsOnly.black_piece_of_get_of_color hKO src p hAtSrc' (by simpa [hToMove] using hTurn)
          cases hSrcEq
          subst hPEq
          have hNoCastleTrue : castleMoveIfLegal gs true = none :=
            KingsOnly.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKO true
          have hNoCastleFalse : castleMoveIfLegal gs false = none :=
            KingsOnly.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKO false
          have hStdMem :
              m ∈
                (Movement.kingTargets bk).filterMap (fun target =>
                  if destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := target } then
                    match gs.board target with
                    | some _ => some { piece := kingPiece Color.Black, fromSq := bk, toSq := target, isCapture := true }
                    | none => some { piece := kingPiece Color.Black, fromSq := bk, toSq := target }
                  else
                    none) := by
            simpa [pieceTargets, kingPiece, hNoCastleTrue, hNoCastleFalse] using hTargets
          rcases List.mem_filterMap.1 hStdMem with ⟨target, hTarget, hSome⟩
          have hFrom : m.fromSq = bk := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hPiece : m.piece = kingPiece Color.Black := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hNoCastle : m.isCastle = false := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hNoEP : m.isEnPassant = false := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hNoPromo : m.promotion = none := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hTo : m.toSq = target := by
            cases hFree :
              destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := target } <;>
                simp [hFree] at hSome
            cases hBoard : gs.board target <;> simp [hFree, hBoard] at hSome
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target } := by
                simpa using hSome.symm
              simp [hEq]
            · have hEq : m = { piece := kingPiece Color.Black, fromSq := bk, toSq := target, isCapture := true } := by
                simpa using hSome.symm
              simp [hEq]
          have hBasic : basicMoveLegalBool gs m = true :=
            basicLegalAndSafe_implies_basicMoveLegalBool gs m hSafe
          have hSquaresDiffer : squaresDiffer m = true := by
            have hb0 := hBasic
            unfold basicMoveLegalBool at hb0
            exact (Eq.mp (Bool.and_eq_true _ _) hb0).2
          have hSafeParts :
              basicMoveLegalBool gs m = true ∧ inCheck (gs.movePiece m).board gs.toMove = false := by
            have hs := hSafe
            unfold basicLegalAndSafe at hs
            simp at hs
            exact hs
          have hSafe' : inCheck (gs.movePiece m).board Color.Black = false := by
            simpa [hToMove] using hSafeParts.2
          -- Destination is not the white king square (king step non-adjacency).
          have hToNeWk : m.toSq ≠ wk := by
            intro hEq
            have hTargetWk : target = wk := by rw [← hTo, hEq]
            have hStep : Movement.isKingStep bk wk :=
              hTargetWk ▸ (Movement.mem_kingTargets_iff bk target).mp hTarget
            exact hNoAdj (Movement.isKingStep_symm bk wk hStep)
          have hMovedBoard :
              (gs.movePiece m).board =
                (gs.board.update bk none).update m.toSq (some (kingPiece Color.Black)) := by
            unfold GameState.movePiece
            simp [hFrom, hPiece, hNoEP, hNoCastle, hNoPromo, GameState.promotedPiece, kingPiece]
          have hBoard' : nxt.board =
              (gs.board.update bk none).update m.toSq (some (kingPiece Color.Black)) := by
            have hNxtBoard : nxt.board = (gs.movePiece m).board := by
              calc
                nxt.board = (GameState.playMove gs m).board := by
                  simpa [hPlay] using congrArg GameState.board hPlay
                _ = (gs.movePiece m).board := by
                  simpa using GameState.playMove_board gs m
            simpa [hNxtBoard] using hMovedBoard
          have hKO' : KingsOnly nxt.board wk m.toSq := by
            constructor
            · -- white king at `wk`
              have hNe1 : wk ≠ bk := hKO.2.2.1
              have hNe2 : wk ≠ m.toSq := by
                intro hEq
                exact hToNeWk hEq.symm
              simp [hBoard', Board.update_ne _ _ _ hNe2, Board.update_ne _ _ _ hNe1, hKO.1]
            constructor
            · -- black king at `m.toSq`
              simp [hBoard', Board.update_eq]
            constructor
            · exact hToNeWk.symm
            · intro sq hNeW hNeB
              by_cases hSqBk : sq = bk
              · cases hSqBk
                have hNe : bk ≠ m.toSq := by
                  have hDiff : m.fromSq ≠ m.toSq := by
                    simpa [squaresDiffer] using hSquaresDiffer
                  intro hEq
                  apply hDiff
                  simp [hFrom, hEq]
                simp [hBoard', Board.update_ne _ _ _ hNe, Board.update_eq]
              · have hNeTo : sq ≠ m.toSq := by simpa using hNeB
                have hNeFrom : sq ≠ bk := hSqBk
                have hStart : gs.board.get sq = none := by
                  exact hKO.2.2.2 sq (by
                    intro hEq
                    subst hEq
                    exact hNeW rfl) hNeFrom
                have hStepTo :
                    ((gs.board.update bk none).update m.toSq (some (kingPiece Color.Black))).get sq =
                      (gs.board.update bk none).get sq := by
                  simpa using
                    (Board.update_ne (gs.board.update bk none) m.toSq (some (kingPiece Color.Black))
                      (target := sq) hNeTo)
                have hStepFrom :
                    (gs.board.update bk none).get sq = gs.board.get sq := by
                  simpa using
                    (Board.update_ne gs.board bk none (target := sq) hNeFrom)
                calc
                  nxt.board.get sq =
                      ((gs.board.update bk none).update m.toSq (some (kingPiece Color.Black))).get sq := by
                        simp [hBoard']
                  _ = (gs.board.update bk none).get sq := hStepTo
                  _ = gs.board.get sq := hStepFrom
                  _ = none := hStart

          have hNoAdj' : ¬ Movement.isKingStep wk m.toSq := by
            intro hStep
            have : inCheck nxt.board Color.Black = true :=
              (KingsOnly.inCheck_black_eq_true_iff_isKingStep hKO').2 hStep
            have hEqBoard : (gs.movePiece m).board = nxt.board :=
              Eq.trans hMovedBoard (hBoard'.symm)
            have : inCheck (gs.movePiece m).board Color.Black = true := by
              simpa [hEqBoard] using this
            simp [hSafe'] at this
          have hInvNxt : KkInv nxt := ⟨wk, m.toSq, hKO', hNoAdj'⟩
          simpa [hnxt] using hInvNxt

theorem KkInv.applyLegalMoves_preserved (gs : GameState) (moves : List Move) (gs' : GameState) :
    KkInv gs →
    applyLegalMoves gs moves = Except.ok gs' →
    KkInv gs' := by
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
      have hInv1 : KkInv gs1 := KkInv.applyLegalMove_preserved gs m gs1 hInv hOk1
      exact ih gs1 hInv1 hOk2

theorem KkInv.isDeadPosition (gs : GameState) :
    KkInv gs → isDeadPosition gs := by
  intro hInv
  intro hContra
  rcases hContra with ⟨moves, gs', hOk, hMate⟩
  have hInv' : KkInv gs' :=
    KkInv.applyLegalMoves_preserved gs moves gs' hInv hOk
  have : isCheckmate gs' = false := KkInv.isCheckmate_false gs' hInv'
  simp [this] at hMate

theorem isDeadPosition_kkGameState (wk bk : Square) (toMove : Color)
    (hNe : wk ≠ bk)
    (hNoAdj : ¬ Movement.isKingStep wk bk) :
    isDeadPosition (kkGameState wk bk toMove) := by
  have hInv : KkInv (kkGameState wk bk toMove) :=
    kkInv_kkGameState wk bk toMove hNe hNoAdj
  exact KkInv.isDeadPosition (kkGameState wk bk toMove) hInv

theorem isDeadPosition_of_KingsOnly (gs : GameState) (wk bk : Square)
    (hKO : KingsOnly gs.board wk bk)
    (hNoAdj : ¬ Movement.isKingStep wk bk) :
    isDeadPosition gs := by
  refine KkInv.isDeadPosition gs ?_
  exact ⟨wk, bk, hKO, hNoAdj⟩

end Rules
end Chess
