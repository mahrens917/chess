import Chess.KMinorDeadPositionInvariants

namespace Chess
namespace Rules

/-!
Specializations of `KMinorInv` for particular single-minor endgames.

These invariants are closed under legal move sequences (either remain in the same endgame family
or collapse to K vs K when the minor is captured).

They are designed to be the entry points for the semantic dead-position theorems:
- K+N vs K
- K+B vs K
-/

def KknInv (gs : GameState) : Prop :=
  ∃ wk bk msq mp,
    KingsPlusMinor gs.board wk bk msq mp ∧
      mp.pieceType = PieceType.Knight ∧
      ¬ Movement.isKingStep wk bk

def KkbInv (gs : GameState) : Prop :=
  ∃ wk bk msq mp,
    KingsPlusMinor gs.board wk bk msq mp ∧
      mp.pieceType = PieceType.Bishop ∧
      ¬ Movement.isKingStep wk bk

def KknOrKkInv (gs : GameState) : Prop :=
  KknInv gs ∨ KkInv gs

def KkbOrKkInv (gs : GameState) : Prop :=
  KkbInv gs ∨ KkInv gs

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

private theorem notInCheck_of_encodedLegal
    (gs : GameState) (m : Move) :
    encodedLegal gs m → inCheck (gs.movePiece m).board gs.toMove = false := by
  rintro ⟨_sq, _p, _hAt, _hTurn, _hTargets, _hPin, hSafe⟩
  unfold basicLegalAndSafe at hSafe
  have : basicMoveLegalBool gs m = true ∧
      !(inCheck (gs.movePiece m).board gs.toMove) = true := by
    simpa [Bool.and_eq_true] using hSafe
  have hNot : !(inCheck (gs.movePiece m).board gs.toMove) = true := this.2
  simpa using hNot

private theorem toMove_eq_of_piece_eq_kingPiece
    (gs : GameState) (m : Move) (c : Color) :
    m ∈ allLegalMoves gs →
    m.piece = kingPiece c →
    gs.toMove = c := by
  intro hMem hPiece
  have hTurnB : turnMatches gs m = true :=
    mem_allLegalMoves_implies_turnMatches gs m hMem
  have hTurnM : m.piece.color = gs.toMove := by
    unfold turnMatches at hTurnB
    exact of_decide_eq_true hTurnB
  -- `kingPiece c` has color `c`.
  have : c = gs.toMove := by
    simpa [hPiece, kingPiece] using hTurnM
  exact this.symm

private theorem applyLegalMove_board_eq_movePiece
    (gs : GameState) (m : Move) (gs' : GameState) :
    applyLegalMove gs m = Except.ok gs' →
    gs'.board = (gs.movePiece m).board := by
  intro hOk
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
      -- Reduce to `playMove_board`.
      have : nxt.board = (gs.movePiece m).board := by
        have : (GameState.playMove gs m).board = (gs.movePiece m).board :=
          GameState.playMove_board gs m
        simpa [hPlay] using this
      simpa [hnxt] using this

theorem KknInv.applyLegalMove_preserved_or_kkInv
    (gs : GameState) (m : Move) (gs' : GameState) :
    KknInv gs →
    applyLegalMove gs m = Except.ok gs' →
    KknOrKkInv gs' := by
  intro hInv hOk
  rcases hInv with ⟨wk, bk, msq, mp, hKPM, hKnight, hNoAdj⟩
  have hBoardEq : gs'.board = (gs.movePiece m).board :=
    applyLegalMove_board_eq_movePiece gs m gs' hOk

  have hMem : m ∈ allLegalMoves gs := by
    -- Same witness extraction as elsewhere: `applyLegalMove? = some` implies `isLegalMove = true`.
    have hOk' := hOk
    unfold applyLegalMove at hOk'
    cases hOpt : applyLegalMove? gs m with
    | none =>
        simp [hOpt] at hOk'
    | some nxt =>
        have hIsLegal : isLegalMove gs m = true := by
          unfold applyLegalMove? at hOpt
          by_cases h : isLegalMove gs m = true
          · exact h
          · simp [h] at hOpt
        unfold isLegalMove at hIsLegal
        rcases (List.any_eq_true).1 hIsLegal with ⟨cand, hCandMem, hCandEq⟩
        have hEq : cand = m := by simpa using hCandEq
        simpa [hEq] using hCandMem

  have hEnc : encodedLegal gs m :=
    (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  have hNotCheck : inCheck (gs.movePiece m).board gs.toMove = false :=
    notInCheck_of_encodedLegal gs m hEnc

  -- Split capture vs non-capture.
  cases hCap : m.isCapture with
  | false =>
      have hPres :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_false_preserves
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
          hKPM hMem hCap
      rcases hPres with ⟨hPiece, hKPM'⟩ | ⟨hPiece, hKPM'⟩ | ⟨hPiece, hKPM'⟩
      · -- white king moved
        have hToMove : gs.toMove = Color.White :=
          toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.White) hMem hPiece
        have hNotCheckW : inCheck (gs.movePiece m).board Color.White = false := by
          simpa [hToMove] using hNotCheck
        have hNoAdj' : ¬ Movement.isKingStep m.toSq bk := by
          intro hAdj
          have hChk : inCheck (gs.movePiece m).board Color.White = true :=
            KingsPlusMinor.inCheck_white_of_isKingStep (h := hKPM')
              (Movement.isKingStep_symm _ _ hAdj)
          have : (true : Bool) = false := by
            simpa [hChk] using hNotCheckW
          cases this
        have hKPMgs' : KingsPlusMinor gs'.board m.toSq bk msq mp := by
          simpa [hBoardEq] using hKPM'
        exact Or.inl ⟨m.toSq, bk, msq, mp, hKPMgs', hKnight, hNoAdj'⟩
      · -- black king moved
        have hToMove : gs.toMove = Color.Black :=
          toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.Black) hMem hPiece
        have hNotCheckB : inCheck (gs.movePiece m).board Color.Black = false := by
          simpa [hToMove] using hNotCheck
        have hNoAdj' : ¬ Movement.isKingStep wk m.toSq := by
          intro hAdj
          have hChk : inCheck (gs.movePiece m).board Color.Black = true :=
            KingsPlusMinor.inCheck_black_of_isKingStep (h := hKPM') hAdj
          have : (true : Bool) = false := by
            simpa [hChk] using hNotCheckB
          cases this
        have hKPMgs' : KingsPlusMinor gs'.board wk m.toSq msq mp := by
          simpa [hBoardEq] using hKPM'
        exact Or.inl ⟨wk, m.toSq, msq, mp, hKPMgs', hKnight, hNoAdj'⟩
      · -- minor moved (knight stays a knight)
        have hKPMgs' : KingsPlusMinor gs'.board wk bk m.toSq mp := by
          simpa [hBoardEq] using hKPM'
        exact Or.inl ⟨wk, bk, m.toSq, mp, hKPMgs', hKnight, hNoAdj⟩
  | true =>
      -- Captures collapse to K vs K (opponent king captures the minor).
      have hTo : m.toSq = msq :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_implies_toSq_minorSquare
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
      have hMover : m.piece = kingPiece mp.color.opposite :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_implies_piece_is_opponentKing
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
      have hFrom :
          m.fromSq = (if mp.color = Color.White then bk else wk) :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_implies_fromSq_opponentKingSquare
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
      cases hC : mp.color with
      | White =>
          have hPiece : m.piece = kingPiece Color.Black := by simpa [hC, Color.opposite] using hMover
          have hFrom' : m.fromSq = bk := by simpa [hC] using hFrom
          have hKO : KingsOnly (gs.movePiece m).board wk msq :=
            KingsPlusMinor.blackKing_captureMinor_yields_kingsOnly
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
              hKPM hMem hPiece hFrom' (by simp [hTo] )
          have hKObs : KingsOnly gs'.board wk msq := by
            simpa [hBoardEq] using hKO
          -- Preserve non-adjacency using safety.
          have hToMove : gs.toMove = Color.Black :=
            toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.Black) hMem hPiece
          have hNotCheckB : inCheck (gs.movePiece m).board Color.Black = false := by
            simpa [hToMove] using hNotCheck
          have hNoAdj' : ¬ Movement.isKingStep wk msq := by
            intro hAdj
            have hChk : inCheck (gs.movePiece m).board Color.Black = true :=
              (KingsOnly.inCheck_black_eq_true_iff_isKingStep hKO).2 hAdj
            have : (true : Bool) = false := by
              simpa [hChk] using hNotCheckB
            cases this
          exact Or.inr ⟨wk, msq, hKObs, hNoAdj'⟩
      | Black =>
          have hPiece : m.piece = kingPiece Color.White := by simpa [hC, Color.opposite] using hMover
          have hFrom' : m.fromSq = wk := by simpa [hC] using hFrom
          have hKO : KingsOnly (gs.movePiece m).board msq bk :=
            KingsPlusMinor.whiteKing_captureMinor_yields_kingsOnly
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
              hKPM hMem hPiece hFrom' (by simp [hTo])
          have hKObs : KingsOnly gs'.board msq bk := by
            simpa [hBoardEq] using hKO
          have hToMove : gs.toMove = Color.White :=
            toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.White) hMem hPiece
          have hNotCheckW : inCheck (gs.movePiece m).board Color.White = false := by
            simpa [hToMove] using hNotCheck
          have hNoAdj' : ¬ Movement.isKingStep msq bk := by
            intro hAdj
            have hChk : inCheck (gs.movePiece m).board Color.White = true :=
              (KingsOnly.inCheck_white_eq_true_iff_isKingStep hKO).2 (Movement.isKingStep_symm _ _ hAdj)
            have : (true : Bool) = false := by
              simpa [hChk] using hNotCheckW
            cases this
          exact Or.inr ⟨msq, bk, hKObs, hNoAdj'⟩

-- K+B is identical: the bishop piece type is preserved in all non-capture branches.
theorem KkbInv.applyLegalMove_preserved_or_kkInv
    (gs : GameState) (m : Move) (gs' : GameState) :
    KkbInv gs →
    applyLegalMove gs m = Except.ok gs' →
    KkbOrKkInv gs' := by
  intro hInv hOk
  rcases hInv with ⟨wk, bk, msq, mp, hKPM, hBishop, hNoAdj⟩
  have hBoardEq : gs'.board = (gs.movePiece m).board :=
    applyLegalMove_board_eq_movePiece gs m gs' hOk
  have hMem : m ∈ allLegalMoves gs := by
    have hOk' := hOk
    unfold applyLegalMove at hOk'
    cases hOpt : applyLegalMove? gs m with
    | none =>
        simp [hOpt] at hOk'
    | some nxt =>
        have hIsLegal : isLegalMove gs m = true := by
          unfold applyLegalMove? at hOpt
          by_cases h : isLegalMove gs m = true
          · exact h
          · simp [h] at hOpt
        unfold isLegalMove at hIsLegal
        rcases (List.any_eq_true).1 hIsLegal with ⟨cand, hCandMem, hCandEq⟩
        have hEq : cand = m := by simpa using hCandEq
        simpa [hEq] using hCandMem
  have hEnc : encodedLegal gs m :=
    (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  have hNotCheck : inCheck (gs.movePiece m).board gs.toMove = false :=
    notInCheck_of_encodedLegal gs m hEnc
  cases hCap : m.isCapture with
  | false =>
      have hPres :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_false_preserves
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
          hKPM hMem hCap
      rcases hPres with ⟨hPiece, hKPM'⟩ | ⟨hPiece, hKPM'⟩ | ⟨hPiece, hKPM'⟩
      · have hToMove : gs.toMove = Color.White :=
          toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.White) hMem hPiece
        have hNotCheckW : inCheck (gs.movePiece m).board Color.White = false := by
          simpa [hToMove] using hNotCheck
        have hNoAdj' : ¬ Movement.isKingStep m.toSq bk := by
          intro hAdj
          have hChk : inCheck (gs.movePiece m).board Color.White = true :=
            KingsPlusMinor.inCheck_white_of_isKingStep (h := hKPM')
              (Movement.isKingStep_symm _ _ hAdj)
          have : (true : Bool) = false := by
            simpa [hChk] using hNotCheckW
          cases this
        have hKPMgs' : KingsPlusMinor gs'.board m.toSq bk msq mp := by
          simpa [hBoardEq] using hKPM'
        exact Or.inl ⟨m.toSq, bk, msq, mp, hKPMgs', hBishop, hNoAdj'⟩
      · have hToMove : gs.toMove = Color.Black :=
          toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.Black) hMem hPiece
        have hNotCheckB : inCheck (gs.movePiece m).board Color.Black = false := by
          simpa [hToMove] using hNotCheck
        have hNoAdj' : ¬ Movement.isKingStep wk m.toSq := by
          intro hAdj
          have hChk : inCheck (gs.movePiece m).board Color.Black = true :=
            KingsPlusMinor.inCheck_black_of_isKingStep (h := hKPM') hAdj
          have : (true : Bool) = false := by
            simpa [hChk] using hNotCheckB
          cases this
        have hKPMgs' : KingsPlusMinor gs'.board wk m.toSq msq mp := by
          simpa [hBoardEq] using hKPM'
        exact Or.inl ⟨wk, m.toSq, msq, mp, hKPMgs', hBishop, hNoAdj'⟩
      · have hKPMgs' : KingsPlusMinor gs'.board wk bk m.toSq mp := by
          simpa [hBoardEq] using hKPM'
        exact Or.inl ⟨wk, bk, m.toSq, mp, hKPMgs', hBishop, hNoAdj⟩
  | true =>
      -- Same capture collapse as K+N.
      have hTo : m.toSq = msq :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_implies_toSq_minorSquare
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
      have hMover : m.piece = kingPiece mp.color.opposite :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_implies_piece_is_opponentKing
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
      have hFrom :
          m.fromSq = (if mp.color = Color.White then bk else wk) :=
        KingsPlusMinor.mem_allLegalMoves_isCapture_implies_fromSq_opponentKingSquare
          (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem (by simpa using hCap)
      cases hC : mp.color with
      | White =>
          have hPiece : m.piece = kingPiece Color.Black := by simpa [hC, Color.opposite] using hMover
          have hFrom' : m.fromSq = bk := by simpa [hC] using hFrom
          have hKO : KingsOnly (gs.movePiece m).board wk msq :=
            KingsPlusMinor.blackKing_captureMinor_yields_kingsOnly
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
              hKPM hMem hPiece hFrom' (by simp [hTo])
          have hKObs : KingsOnly gs'.board wk msq := by
            simpa [hBoardEq] using hKO
          have hToMove : gs.toMove = Color.Black :=
            toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.Black) hMem hPiece
          have hNotCheckB : inCheck (gs.movePiece m).board Color.Black = false := by
            simpa [hToMove] using hNotCheck
          have hNoAdj' : ¬ Movement.isKingStep wk msq := by
            intro hAdj
            have hChk : inCheck (gs.movePiece m).board Color.Black = true :=
              (KingsOnly.inCheck_black_eq_true_iff_isKingStep hKO).2 hAdj
            have : (true : Bool) = false := by
              simpa [hChk] using hNotCheckB
            cases this
          exact Or.inr ⟨wk, msq, hKObs, hNoAdj'⟩
      | Black =>
          have hPiece : m.piece = kingPiece Color.White := by simpa [hC, Color.opposite] using hMover
          have hFrom' : m.fromSq = wk := by simpa [hC] using hFrom
          have hKO : KingsOnly (gs.movePiece m).board msq bk :=
            KingsPlusMinor.whiteKing_captureMinor_yields_kingsOnly
              (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp)
              hKPM hMem hPiece hFrom' (by simp [hTo])
          have hKObs : KingsOnly gs'.board msq bk := by
            simpa [hBoardEq] using hKO
          have hToMove : gs.toMove = Color.White :=
            toMove_eq_of_piece_eq_kingPiece (gs := gs) (m := m) (c := Color.White) hMem hPiece
          have hNotCheckW : inCheck (gs.movePiece m).board Color.White = false := by
            simpa [hToMove] using hNotCheck
          have hNoAdj' : ¬ Movement.isKingStep msq bk := by
            intro hAdj
            have hChk : inCheck (gs.movePiece m).board Color.White = true :=
              (KingsOnly.inCheck_white_eq_true_iff_isKingStep hKO).2 (Movement.isKingStep_symm _ _ hAdj)
            have : (true : Bool) = false := by
              simpa [hChk] using hNotCheckW
            cases this
          exact Or.inr ⟨msq, bk, hKObs, hNoAdj'⟩

theorem KknOrKkInv.applyLegalMove_preserved
    (gs : GameState) (m : Move) (gs' : GameState) :
    KknOrKkInv gs →
    applyLegalMove gs m = Except.ok gs' →
    KknOrKkInv gs' := by
  intro hInv hOk
  rcases hInv with hKkn | hKk
  · exact KknInv.applyLegalMove_preserved_or_kkInv gs m gs' hKkn hOk
  · exact Or.inr (KkInv.applyLegalMove_preserved gs m gs' hKk hOk)

theorem KkbOrKkInv.applyLegalMove_preserved
    (gs : GameState) (m : Move) (gs' : GameState) :
    KkbOrKkInv gs →
    applyLegalMove gs m = Except.ok gs' →
    KkbOrKkInv gs' := by
  intro hInv hOk
  rcases hInv with hKkb | hKk
  · exact KkbInv.applyLegalMove_preserved_or_kkInv gs m gs' hKkb hOk
  · exact Or.inr (KkInv.applyLegalMove_preserved gs m gs' hKk hOk)

theorem KknOrKkInv.applyLegalMoves_preserved
    (gs : GameState) (moves : List Move) (gs' : GameState) :
    KknOrKkInv gs →
    applyLegalMoves gs moves = Except.ok gs' →
    KknOrKkInv gs' := by
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
      have hInv1 : KknOrKkInv gs1 :=
        KknOrKkInv.applyLegalMove_preserved gs m gs1 hInv hOk1
      exact ih gs1 hInv1 hOk2

theorem KkbOrKkInv.applyLegalMoves_preserved
    (gs : GameState) (moves : List Move) (gs' : GameState) :
    KkbOrKkInv gs →
    applyLegalMoves gs moves = Except.ok gs' →
    KkbOrKkInv gs' := by
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
      have hInv1 : KkbOrKkInv gs1 :=
        KkbOrKkInv.applyLegalMove_preserved gs m gs1 hInv hOk1
      exact ih gs1 hInv1 hOk2

end Rules
end Chess
