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

/-- In a K+N vs K position, after the white king moves from wk to esc (a non-capture),
    the resulting board is a K+N board with white king at esc. -/
private theorem KingsPlusMinor_after_white_king_move
    {b : Board} {wk bk msq : Square} {mp : Piece} {esc : Square}
    (hKPM : KingsPlusMinor b wk bk msq mp)
    (hEscNeWk : esc ≠ wk)
    (hEscNeBk : esc ≠ bk)
    (hEscNeMsq : esc ≠ msq)
    (hEmpty : b.get esc = none) :
    KingsPlusMinor ((b.update wk none).update esc (some (kingPiece Color.White))) esc bk msq mp := by
  constructor
  · -- white king at esc
    simp [Board.update_eq]
  constructor
  · -- black king at bk
    have hBkNeWk : bk ≠ wk := hKPM.2.2.2.1.symm
    simp [Board.update_ne _ _ _ hEscNeBk.symm, Board.update_ne _ _ _ hBkNeWk, hKPM.2.1]
  constructor
  · -- minor at msq
    have hMsqNeWk : msq ≠ wk := hKPM.2.2.2.2.1.symm
    simp [Board.update_ne _ _ _ hEscNeMsq.symm, Board.update_ne _ _ _ hMsqNeWk, hKPM.2.2.1]
  constructor
  · -- esc ≠ bk
    exact hEscNeBk
  constructor
  · -- esc ≠ msq
    exact hEscNeMsq
  constructor
  · -- bk ≠ msq (unchanged)
    exact hKPM.2.2.2.2.2.1
  · -- all other squares empty
    intro sq hSqNeEsc hSqNeBk hSqNeMsq
    by_cases hSqWk : sq = wk
    · simp [hSqWk, Board.update_ne _ _ _ hEscNeWk.symm, Board.update_eq]
    · have hOrig := hKPM.2.2.2.2.2.2 sq hSqWk hSqNeBk hSqNeMsq
      simp [Board.update_ne _ _ _ (Ne.symm hSqNeEsc), Board.update_ne _ _ _ hSqWk, hOrig]

/-- In a K+N vs K position, after the black king moves from bk to esc (a non-capture),
    the resulting board is a K+N board with black king at esc. -/
private theorem KingsPlusMinor_after_black_king_move
    {b : Board} {wk bk msq : Square} {mp : Piece} {esc : Square}
    (hKPM : KingsPlusMinor b wk bk msq mp)
    (hEscNeWk : esc ≠ wk)
    (hEscNeBk : esc ≠ bk)
    (hEscNeMsq : esc ≠ msq)
    (hEmpty : b.get esc = none) :
    KingsPlusMinor ((b.update bk none).update esc (some (kingPiece Color.Black))) wk esc msq mp := by
  constructor
  · -- white king at wk
    have hWkNeBk : wk ≠ bk := hKPM.2.2.2.1
    simp [Board.update_ne _ _ _ hEscNeWk.symm, Board.update_ne _ _ _ hWkNeBk, hKPM.1]
  constructor
  · -- black king at esc
    simp [Board.update_eq]
  constructor
  · -- minor at msq
    have hMsqNeBk : msq ≠ bk := hKPM.2.2.2.2.2.1.symm
    simp [Board.update_ne _ _ _ hEscNeMsq.symm, Board.update_ne _ _ _ hMsqNeBk, hKPM.2.2.1]
  constructor
  · -- wk ≠ esc
    exact hEscNeWk.symm
  constructor
  · -- wk ≠ msq (unchanged)
    exact hKPM.2.2.2.2.1
  constructor
  · -- esc ≠ msq
    exact hEscNeMsq
  · -- all other squares empty
    intro sq hSqNeWk hSqNeEsc hSqNeMsq
    by_cases hSqBk : sq = bk
    · simp [hSqBk, Board.update_ne _ _ _ hEscNeBk.symm, Board.update_eq]
    · have hOrig := hKPM.2.2.2.2.2.2 sq hSqNeWk hSqBk hSqNeMsq
      simp [Board.update_ne _ _ _ (Ne.symm hSqNeEsc), Board.update_ne _ _ _ hSqBk, hOrig]

/-- After white king moves in a K+N position, if the target is not attacked by black king
    or knight, then white is not in check. -/
private theorem KingsPlusMinor_white_not_in_check_after_move
    {b : Board} {wk bk msq : Square} {mp : Piece} {esc : Square}
    (hKPM : KingsPlusMinor b wk bk msq mp)
    (hKnight : mp.pieceType = PieceType.Knight)
    (hMpBlack : mp.color = Color.Black)
    (hEscNeWk : esc ≠ wk)
    (hEscNeBk : esc ≠ bk)
    (hEscNeMsq : esc ≠ msq)
    (hEmpty : b.get esc = none)
    (hNotAdjBk : ¬ Movement.isKingStep esc bk)
    (hNotKnight : ¬ Movement.isKnightMove msq esc) :
    inCheck ((b.update wk none).update esc (some (kingPiece Color.White))) Color.White = false := by
  let b' := (b.update wk none).update esc (some (kingPiece Color.White))
  have hKPM' : KingsPlusMinor b' esc bk msq mp :=
    KingsPlusMinor_after_white_king_move hKPM hEscNeWk hEscNeBk hEscNeMsq hEmpty
  -- Use contrapositive: if inCheck = true, then either black king or knight attacks esc
  by_contra hContra
  push_neg at hContra
  have hChk : inCheck b' Color.White = true := by simpa using hContra
  -- Since esc and bk are not adjacent (hNotAdjBk means black king doesn't attack esc),
  -- and we need to show the minor doesn't attack either.
  -- Use the implies_minor_attacker lemma (but we need the no-adjacency precondition)
  have hNoAdj' : ¬ Movement.isKingStep esc bk := hNotAdjBk
  have ⟨_, hAtk⟩ := KingsPlusMinor.inCheck_white_implies_minor_attacker hKPM' hNoAdj' hChk
  -- attacksSpec for knight is isKnightMove
  have hKnightAttacksEsc : Movement.isKnightMove msq esc := by
    unfold attacksSpec at hAtk
    simp only [hKnight] at hAtk
    exact hAtk
  exact hNotKnight hKnightAttacksEsc

/-- After black king moves in a K+N position, if the target is not attacked by white king
    or knight, then black is not in check. -/
private theorem KingsPlusMinor_black_not_in_check_after_move
    {b : Board} {wk bk msq : Square} {mp : Piece} {esc : Square}
    (hKPM : KingsPlusMinor b wk bk msq mp)
    (hKnight : mp.pieceType = PieceType.Knight)
    (hMpWhite : mp.color = Color.White)
    (hEscNeWk : esc ≠ wk)
    (hEscNeBk : esc ≠ bk)
    (hEscNeMsq : esc ≠ msq)
    (hEmpty : b.get esc = none)
    (hNotAdjWk : ¬ Movement.isKingStep wk esc)
    (hNotKnight : ¬ Movement.isKnightMove msq esc) :
    inCheck ((b.update bk none).update esc (some (kingPiece Color.Black))) Color.Black = false := by
  let b' := (b.update bk none).update esc (some (kingPiece Color.Black))
  have hKPM' : KingsPlusMinor b' wk esc msq mp :=
    KingsPlusMinor_after_black_king_move hKPM hEscNeWk hEscNeBk hEscNeMsq hEmpty
  by_contra hContra
  push_neg at hContra
  have hChk : inCheck b' Color.Black = true := by simpa using hContra
  have hNoAdj' : ¬ Movement.isKingStep wk esc := hNotAdjWk
  have ⟨_, hAtk⟩ := KingsPlusMinor.inCheck_black_implies_minor_attacker hKPM' hNoAdj' hChk
  have hKnightAttacksEsc : Movement.isKnightMove msq esc := by
    unfold attacksSpec at hAtk
    simp only [hKnight] at hAtk
    exact hAtk
  exact hNotKnight hKnightAttacksEsc

/-- In a K+N vs K position, the escape square from the knight is empty. -/
private theorem escape_square_empty_knight
    {b : Board} {wk bk msq : Square} {mp : Piece} {esc : Square}
    (hKPM : KingsPlusMinor b wk bk msq mp)
    (hEscNeWk : esc ≠ wk)
    (hEscNeBk : esc ≠ bk)
    (hEscNeMsq : esc ≠ msq) :
    b.get esc = none :=
  hKPM.2.2.2.2.2.2 esc hEscNeWk hEscNeBk hEscNeMsq

/-- Core geometric lemma: In a K+N vs K position where the defending king is in check,
    there exists at least one escape square.

    This is the fundamental chess fact that K+N cannot deliver checkmate:
    - The knight attacks at most 8 L-shaped squares (non-adjacent to the knight)
    - The attacking king attacks at most 8 adjacent squares
    - But the attacking king must stay at distance ≥ 2 from the defending king
    - Therefore, at least one of the defending king's 8 adjacent squares is safe

    PROOF COMPLEXITY: A full formal proof requires extensive geometric case analysis
    on the 8×8 board, handling corner cases where the king has fewer than 8 adjacent squares.
    The proof would need to show for each of the 64 possible king positions, when in check
    from a knight, at least one escape exists. -/
private theorem knight_check_has_escape (gs : GameState) (wk bk msq : Square) (mp : Piece)
    (hKPM : KingsPlusMinor gs.board wk bk msq mp)
    (hKnight : mp.pieceType = PieceType.Knight)
    (hNoAdj : ¬ Movement.isKingStep wk bk)
    (hInCheck : inCheckStatus gs = true) :
    noLegalMoves gs = false := by
  -- Identify the defending king based on whose turn it is
  have hWkNeBk := hKPM.2.2.2.1
  cases hTurn : gs.toMove with
  | White =>
    -- White to move, in check from knight
    -- Use KingsPlusMinor.inCheck_white_implies_minor_attacker
    have hChk : inCheck gs.board Color.White = true := by simpa [inCheckStatus, hTurn] using hInCheck
    have ⟨hKnightBlack, hAtk⟩ := KingsPlusMinor.inCheck_white_implies_minor_attacker hKPM hNoAdj hChk
    -- attacksSpec for knight is exactly isKnightMove
    have hKnightAttacksWk : Movement.isKnightMove msq wk := by
      unfold attacksSpec at hAtk
      simp only [hKnight] at hAtk
      exact hAtk
    -- Get escape square from geometric lemma
    obtain ⟨esc, hEscAdj, hEscNotAdjBk, hEscNotKnight⟩ :=
      Movement.exists_safe_escape_from_knight wk bk msq hWkNeBk hNoAdj hKnightAttacksWk
    -- Now construct the king move from wk to esc and show it's legal
    let m : Move := { piece := kingPiece Color.White, fromSq := wk, toSq := esc }
    -- Establish that esc is different from all occupied squares
    have hEscNeWk : esc ≠ wk := hEscAdj.1.symm
    have hEscNeBk : esc ≠ bk := by
      intro hEq
      rw [hEq] at hEscAdj
      exact hNoAdj (Movement.isKingStep_symm bk wk hEscAdj)
    have hEscNeMsq : esc ≠ msq := by
      intro hEq
      rw [hEq] at hEscAdj
      have hNotStep := Movement.isKnightMove_not_isKingStep msq wk hKnightAttacksWk
      exact hNotStep (Movement.isKingStep_symm msq wk hEscAdj)
    have hEscEmpty : gs.board.get esc = none :=
      escape_square_empty_knight hKPM hEscNeWk hEscNeBk hEscNeMsq
    -- Show m ∈ allLegalMoves gs via encodedLegal
    have hMem : m ∈ allLegalMoves gs := by
      rw [mem_allLegalMoves_iff_encodedLegal]
      refine ⟨wk, kingPiece Color.White, ?_, ?_, ?_, ?_, ?_⟩
      · -- gs.board wk = some (kingPiece Color.White)
        exact hKPM.1
      · -- (kingPiece Color.White).color = gs.toMove
        simp [kingPiece, hTurn]
      · -- m ∈ pieceTargets gs wk (kingPiece Color.White)
        unfold pieceTargets
        simp only [kingPiece, PieceType.King]
        -- Standard king moves: filterMap over kingTargets
        have hNoCastleTrue : castleMoveIfLegal gs true = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM true
        have hNoCastleFalse : castleMoveIfLegal gs false = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM false
        simp only [hNoCastleTrue, hNoCastleFalse, List.filterMap_nil, List.append_nil]
        -- esc is in kingTargets wk
        have hTarget : esc ∈ Movement.kingTargets wk := by
          rw [Movement.mem_kingTargets_iff]
          exact hEscAdj
        -- destinationFriendlyFree for escape square
        have hDestFree : destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := esc } = true := by
          unfold destinationFriendlyFree
          cases hAt : gs.board esc with
          | none => rfl
          | some p =>
            have hEsc' : gs.board.get esc = some p := by simpa using hAt
            have : gs.board.get esc = none := hEscEmpty
            simp_all
        apply List.mem_filterMap.2
        refine ⟨esc, hTarget, ?_⟩
        simp only [hDestFree]
        -- esc is empty so not a capture
        cases hBoard : gs.board esc with
        | none => simp
        | some p =>
          have hEsc' : gs.board.get esc = some p := by simpa using hBoard
          simp_all
      · -- respectsPin (pinnedSquares gs gs.toMove) m = true
        -- King moves always respect pins (king cannot be pinned)
        unfold respectsPin
        -- Need to show the fromSq (wk) is not in pinnedSquares
        -- Even if it were, king moves pass the direction check
        cases hFind : (pinnedSquares gs gs.toMove).find? (fun p => p.fst = wk) with
        | none => rfl
        | some pinPair =>
          -- King step means file/rank diff ≤ 1, so passes the pin filter
          have ⟨_, hf, hr⟩ := hEscAdj
          have hFileDiff : Movement.absInt (Movement.fileDiff wk esc) ≤ 1 := hf
          have hRankDiff : Movement.absInt (Movement.rankDiff wk esc) ≤ 1 := hr
          -- Either fd = 0, rd = 0, or fd = rd for a king step
          by_cases hFd0 : Movement.absInt (Movement.fileDiff wk esc) = 0
          · simp [hFd0]
          · by_cases hRd0 : Movement.absInt (Movement.rankDiff wk esc) = 0
            · simp [hRd0]
            · -- Both diffs are 1 (diagonal)
              have hFd1 : Movement.absInt (Movement.fileDiff wk esc) = 1 := by omega
              have hRd1 : Movement.absInt (Movement.rankDiff wk esc) = 1 := by omega
              simp [hFd1, hRd1]
      · -- basicLegalAndSafe gs m = true
        unfold basicLegalAndSafe
        constructor
        · -- basicMoveLegalBool
          unfold basicMoveLegalBool
          have hOrigin : originHasPiece gs m = true := by
            unfold originHasPiece
            simp [hKPM.1]
          have hTurnM : turnMatches gs m = true := by
            unfold turnMatches
            simp [kingPiece, hTurn]
          have hDestFree : destinationFriendlyFree gs m = true := by
            unfold destinationFriendlyFree
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hCapFlag : captureFlagConsistent gs m = true := by
            unfold captureFlagConsistent
            -- m.isCapture defaults to false, esc is empty
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hSqDiff : squaresDiffer m = true := by
            unfold squaresDiffer
            simp [hEscNeWk.symm]
          simp [hOrigin, hTurnM, hDestFree, hCapFlag, hSqDiff]
        · -- !(inCheck (gs.movePiece m).board gs.toMove)
          simp only [Bool.not_eq_true']
          -- Show the board after move
          have hBoard' : (gs.movePiece m).board =
              (gs.board.update wk none).update esc (some (kingPiece Color.White)) := by
            unfold GameState.movePiece
            simp [kingPiece]
          rw [hBoard', hTurn]
          have hNotAdjEscBk : ¬ Movement.isKingStep esc bk := by
            intro h
            exact hEscNotAdjBk (Movement.isKingStep_symm esc bk h)
          exact KingsPlusMinor_white_not_in_check_after_move
            hKPM hKnight hKnightBlack hEscNeWk hEscNeBk hEscNeMsq hEscEmpty
            hNotAdjEscBk hEscNotKnight
    have hNe : allLegalMoves gs ≠ [] := List.ne_nil_of_mem hMem
    exact List.isEmpty_eq_false_iff.mpr hNe
  | Black =>
    -- Black to move, in check from knight
    have hChk : inCheck gs.board Color.Black = true := by simpa [inCheckStatus, hTurn] using hInCheck
    have ⟨hKnightWhite, hAtk⟩ := KingsPlusMinor.inCheck_black_implies_minor_attacker hKPM hNoAdj hChk
    have hKnightAttacksBk : Movement.isKnightMove msq bk := by
      unfold attacksSpec at hAtk
      simp only [hKnight] at hAtk
      exact hAtk
    have hNoAdjBkWk : ¬ Movement.isKingStep bk wk := by
      intro h
      exact hNoAdj (Movement.isKingStep_symm bk wk h)
    obtain ⟨esc, hEscAdj, hEscNotAdjWk, hEscNotKnight⟩ :=
      Movement.exists_safe_escape_from_knight bk wk msq hWkNeBk.symm hNoAdjBkWk hKnightAttacksBk
    -- Now construct the king move from bk to esc and show it's legal
    let m : Move := { piece := kingPiece Color.Black, fromSq := bk, toSq := esc }
    -- Establish that esc is different from all occupied squares
    have hEscNeBk : esc ≠ bk := hEscAdj.1.symm
    have hEscNeWk : esc ≠ wk := by
      intro hEq
      rw [hEq] at hEscAdj
      exact hNoAdjBkWk hEscAdj
    have hEscNeMsq : esc ≠ msq := by
      intro hEq
      rw [hEq] at hEscAdj
      have hNotStep := Movement.isKnightMove_not_isKingStep msq bk hKnightAttacksBk
      exact hNotStep (Movement.isKingStep_symm msq bk hEscAdj)
    have hEscEmpty : gs.board.get esc = none :=
      escape_square_empty_knight hKPM hEscNeWk hEscNeBk hEscNeMsq
    -- Show m ∈ allLegalMoves gs via encodedLegal
    have hMem : m ∈ allLegalMoves gs := by
      rw [mem_allLegalMoves_iff_encodedLegal]
      refine ⟨bk, kingPiece Color.Black, ?_, ?_, ?_, ?_, ?_⟩
      · -- gs.board bk = some (kingPiece Color.Black)
        exact hKPM.2.1
      · -- (kingPiece Color.Black).color = gs.toMove
        simp [kingPiece, hTurn]
      · -- m ∈ pieceTargets gs bk (kingPiece Color.Black)
        unfold pieceTargets
        simp only [kingPiece, PieceType.King]
        have hNoCastleTrue : castleMoveIfLegal gs true = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM true
        have hNoCastleFalse : castleMoveIfLegal gs false = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM false
        simp only [hNoCastleTrue, hNoCastleFalse, List.filterMap_nil, List.append_nil]
        have hTarget : esc ∈ Movement.kingTargets bk := by
          rw [Movement.mem_kingTargets_iff]
          exact hEscAdj
        have hDestFree : destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := esc } = true := by
          unfold destinationFriendlyFree
          cases hAt : gs.board esc with
          | none => rfl
          | some p =>
            have hEsc' : gs.board.get esc = some p := by simpa using hAt
            simp_all
        apply List.mem_filterMap.2
        refine ⟨esc, hTarget, ?_⟩
        simp only [hDestFree]
        cases hBoard : gs.board esc with
        | none => simp
        | some p =>
          have hEsc' : gs.board.get esc = some p := by simpa using hBoard
          simp_all
      · -- respectsPin (pinnedSquares gs gs.toMove) m = true
        unfold respectsPin
        cases hFind : (pinnedSquares gs gs.toMove).find? (fun p => p.fst = bk) with
        | none => rfl
        | some pinPair =>
          have ⟨_, hf, hr⟩ := hEscAdj
          have hFileDiff : Movement.absInt (Movement.fileDiff bk esc) ≤ 1 := hf
          have hRankDiff : Movement.absInt (Movement.rankDiff bk esc) ≤ 1 := hr
          by_cases hFd0 : Movement.absInt (Movement.fileDiff bk esc) = 0
          · simp [hFd0]
          · by_cases hRd0 : Movement.absInt (Movement.rankDiff bk esc) = 0
            · simp [hRd0]
            · have hFd1 : Movement.absInt (Movement.fileDiff bk esc) = 1 := by omega
              have hRd1 : Movement.absInt (Movement.rankDiff bk esc) = 1 := by omega
              simp [hFd1, hRd1]
      · -- basicLegalAndSafe gs m = true
        unfold basicLegalAndSafe
        constructor
        · -- basicMoveLegalBool
          unfold basicMoveLegalBool
          have hOrigin : originHasPiece gs m = true := by
            unfold originHasPiece
            simp [hKPM.2.1]
          have hTurnM : turnMatches gs m = true := by
            unfold turnMatches
            simp [kingPiece, hTurn]
          have hDestFree : destinationFriendlyFree gs m = true := by
            unfold destinationFriendlyFree
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hCapFlag : captureFlagConsistent gs m = true := by
            unfold captureFlagConsistent
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hSqDiff : squaresDiffer m = true := by
            unfold squaresDiffer
            simp [hEscNeBk.symm]
          simp [hOrigin, hTurnM, hDestFree, hCapFlag, hSqDiff]
        · -- !(inCheck (gs.movePiece m).board gs.toMove)
          simp only [Bool.not_eq_true']
          have hBoard' : (gs.movePiece m).board =
              (gs.board.update bk none).update esc (some (kingPiece Color.Black)) := by
            unfold GameState.movePiece
            simp [kingPiece]
          rw [hBoard', hTurn]
          have hNotAdjWkEsc : ¬ Movement.isKingStep wk esc := by
            intro h
            exact hEscNotAdjWk (Movement.isKingStep_symm wk esc h)
          exact KingsPlusMinor_black_not_in_check_after_move
            hKPM hKnight hKnightWhite hEscNeWk hEscNeBk hEscNeMsq hEscEmpty
            hNotAdjWkEsc hEscNotKnight
    have hNe : allLegalMoves gs ≠ [] := List.ne_nil_of_mem hMem
    exact List.isEmpty_eq_false_iff.mpr hNe

/-- K+N vs K positions cannot be checkmate.
    Either not in check, or if in check, there's always an escape. -/
theorem KknInv.isCheckmate_false (gs : GameState) :
    KknInv gs → isCheckmate gs = false := by
  intro hInv
  rcases hInv with ⟨wk, bk, msq, mp, hKPM, hKnight, hNoAdj⟩
  unfold isCheckmate
  by_cases hChk : inCheckStatus gs = true
  · -- In check: show there's a legal move (escape)
    have hMoves : noLegalMoves gs = false :=
      knight_check_has_escape gs wk bk msq mp hKPM hKnight hNoAdj hChk
    simp [hMoves]
  · -- Not in check: checkmate requires being in check
    simp [hChk]

/-- K+N or K vs K positions cannot be checkmate. -/
theorem KknOrKkInv.isCheckmate_false (gs : GameState) :
    KknOrKkInv gs → isCheckmate gs = false := by
  intro hInv
  rcases hInv with hKkn | hKk
  · exact KknInv.isCheckmate_false gs hKkn
  · exact KkInv.isCheckmate_false gs hKk

/-- K+N or K vs K positions are dead positions (no checkmate reachable). -/
theorem KknOrKkInv.isDeadPosition (gs : GameState) :
    KknOrKkInv gs → isDeadPosition gs := by
  intro hInv
  intro hContra
  rcases hContra with ⟨moves, gs', hOk, hMate⟩
  have hInv' : KknOrKkInv gs' :=
    KknOrKkInv.applyLegalMoves_preserved gs moves gs' hInv hOk
  have : isCheckmate gs' = false := KknOrKkInv.isCheckmate_false gs' hInv'
  simp [this] at hMate

/-- After white king moves in a K+B position, if the target is not attacked by black king
    or bishop, then white is not in check. -/
private theorem KingsPlusMinor_white_not_in_check_after_move_bishop
    {b : Board} {wk bk msq : Square} {mp : Piece} {esc : Square}
    (hKPM : KingsPlusMinor b wk bk msq mp)
    (hBishop : mp.pieceType = PieceType.Bishop)
    (hMpBlack : mp.color = Color.Black)
    (hEscNeWk : esc ≠ wk)
    (hEscNeBk : esc ≠ bk)
    (hEscNeMsq : esc ≠ msq)
    (hEmpty : b.get esc = none)
    (hNotAdjBk : ¬ Movement.isKingStep esc bk)
    (hNotBishop : ¬ (msq ≠ esc ∧ Movement.isDiagonal msq esc)) :
    inCheck ((b.update wk none).update esc (some (kingPiece Color.White))) Color.White = false := by
  let b' := (b.update wk none).update esc (some (kingPiece Color.White))
  have hKPM' : KingsPlusMinor b' esc bk msq mp :=
    KingsPlusMinor_after_white_king_move hKPM hEscNeWk hEscNeBk hEscNeMsq hEmpty
  by_contra hContra
  push_neg at hContra
  have hChk : inCheck b' Color.White = true := by simpa using hContra
  have hNoAdj' : ¬ Movement.isKingStep esc bk := hNotAdjBk
  have ⟨_, hAtk⟩ := KingsPlusMinor.inCheck_white_implies_minor_attacker hKPM' hNoAdj' hChk
  -- attacksSpec for bishop is isDiagonal with path clear
  -- Since we only have the minor on the board (empty positions), path is clear if diagonal
  have hBishopAttacksEsc : msq ≠ esc ∧ Movement.isDiagonal msq esc := by
    unfold attacksSpec at hAtk
    simp only [hBishop] at hAtk
    have ⟨hDiag, hPath⟩ := hAtk
    exact ⟨hEscNeMsq.symm, hDiag⟩
  exact hNotBishop hBishopAttacksEsc

/-- After black king moves in a K+B position, if the target is not attacked by white king
    or bishop, then black is not in check. -/
private theorem KingsPlusMinor_black_not_in_check_after_move_bishop
    {b : Board} {wk bk msq : Square} {mp : Piece} {esc : Square}
    (hKPM : KingsPlusMinor b wk bk msq mp)
    (hBishop : mp.pieceType = PieceType.Bishop)
    (hMpWhite : mp.color = Color.White)
    (hEscNeWk : esc ≠ wk)
    (hEscNeBk : esc ≠ bk)
    (hEscNeMsq : esc ≠ msq)
    (hEmpty : b.get esc = none)
    (hNotAdjWk : ¬ Movement.isKingStep wk esc)
    (hNotBishop : ¬ (msq ≠ esc ∧ Movement.isDiagonal msq esc)) :
    inCheck ((b.update bk none).update esc (some (kingPiece Color.Black))) Color.Black = false := by
  let b' := (b.update bk none).update esc (some (kingPiece Color.Black))
  have hKPM' : KingsPlusMinor b' wk esc msq mp :=
    KingsPlusMinor_after_black_king_move hKPM hEscNeWk hEscNeBk hEscNeMsq hEmpty
  by_contra hContra
  push_neg at hContra
  have hChk : inCheck b' Color.Black = true := by simpa using hContra
  have hNoAdj' : ¬ Movement.isKingStep wk esc := hNotAdjWk
  have ⟨_, hAtk⟩ := KingsPlusMinor.inCheck_black_implies_minor_attacker hKPM' hNoAdj' hChk
  have hBishopAttacksEsc : msq ≠ esc ∧ Movement.isDiagonal msq esc := by
    unfold attacksSpec at hAtk
    simp only [hBishop] at hAtk
    have ⟨hDiag, hPath⟩ := hAtk
    exact ⟨hEscNeMsq.symm, hDiag⟩
  exact hNotBishop hBishopAttacksEsc

/-- Similar structure for K+B: bishop check always has escape to opposite color. -/
private theorem bishop_check_has_escape (gs : GameState) (wk bk msq : Square) (mp : Piece)
    (hKPM : KingsPlusMinor gs.board wk bk msq mp)
    (hBishop : mp.pieceType = PieceType.Bishop)
    (hNoAdj : ¬ Movement.isKingStep wk bk)
    (hInCheck : inCheckStatus gs = true) :
    noLegalMoves gs = false := by
  have hWkNeBk := hKPM.2.2.2.1
  cases hTurn : gs.toMove with
  | White =>
    -- White to move, in check from bishop
    have hChk : inCheck gs.board Color.White = true := by simpa [inCheckStatus, hTurn] using hInCheck
    have ⟨hBishopBlack, hAtk⟩ := KingsPlusMinor.inCheck_white_implies_minor_attacker hKPM hNoAdj hChk
    -- attacksSpec for bishop is isDiagonal with path clear
    have hBishopAttacksWk : msq ≠ wk ∧ Movement.isDiagonal msq wk := by
      unfold attacksSpec at hAtk
      simp only [hBishop] at hAtk
      have ⟨hDiag, hPath⟩ := hAtk
      exact ⟨hKPM.2.2.2.2.1.symm, hDiag⟩
    -- Get escape square from geometric lemma
    obtain ⟨esc, hEscAdj, hEscNotAdjBk, hEscNotBishop⟩ :=
      Movement.exists_safe_escape_from_bishop wk bk msq hWkNeBk hNoAdj hBishopAttacksWk
    -- Construct the king move
    let m : Move := { piece := kingPiece Color.White, fromSq := wk, toSq := esc }
    -- Establish that esc is different from all occupied squares
    have hEscNeWk : esc ≠ wk := hEscAdj.1.symm
    have hEscNeBk : esc ≠ bk := by
      intro hEq
      rw [hEq] at hEscAdj
      exact hNoAdj (Movement.isKingStep_symm bk wk hEscAdj)
    have hEscNeMsq : esc ≠ msq := by
      -- The escape is not on the bishop's diagonal (or equals bishop square)
      -- If esc = msq, then either the condition fails or esc ≠ msq is vacuously true
      by_contra hEq
      rw [hEq] at hEscNotBishop
      -- hEscNotBishop : ¬(msq ≠ msq ∧ isDiagonal msq msq)
      -- This should be satisfied (msq ≠ msq is false), so contradiction impossible
      -- Actually, ¬(false ∧ _) is true, so this doesn't give us hEscNeMsq directly
      -- We need another approach: the escape is adjacent to wk (king step), but
      -- the bishop attacks diagonally from msq. If esc = msq, then wk is a king step
      -- from msq, but wk is attacked by bishop diagonally. Diagonal and king step
      -- are compatible (diagonal king step), so this doesn't give contradiction.
      -- Actually, the bishop at msq attacks wk diagonally. If esc = msq, we need to show
      -- this is impossible. The escape square is adjacent to wk, and if esc = msq,
      -- then msq is adjacent to wk. But the bishop attacks from msq to wk diagonally,
      -- meaning they're on the same diagonal but not necessarily adjacent.
      -- A diagonal attack requires distance > 0 in both file and rank with equal deltas.
      -- A king step is Chebyshev distance = 1.
      -- So if msq and wk are diagonal AND king step, they're diagonally adjacent.
      -- This is possible (e.g., e4 to d3). So esc = msq is geometrically possible.
      -- But esc would be the bishop square itself, which is occupied.
      -- Since the escape square needs to be empty, esc ≠ msq.
      have hEscEmpty := escape_square_empty_knight hKPM hEscNeWk hEscNeBk (by exact hEq)
      -- Wait, that's for knight. The escape_square_empty_knight should work for any minor.
      rw [hEq] at hEscNeWk hEscNeBk
      -- hEscEmpty tells us gs.board.get msq = none, but we know msq has the minor
      have hMsqOcc : gs.board.get msq = some mp := hKPM.2.2.1
      simp_all
    have hEscEmpty : gs.board.get esc = none :=
      escape_square_empty_knight hKPM hEscNeWk hEscNeBk hEscNeMsq
    -- Show m ∈ allLegalMoves gs via encodedLegal
    have hMem : m ∈ allLegalMoves gs := by
      rw [mem_allLegalMoves_iff_encodedLegal]
      refine ⟨wk, kingPiece Color.White, ?_, ?_, ?_, ?_, ?_⟩
      · exact hKPM.1
      · simp [kingPiece, hTurn]
      · -- m ∈ pieceTargets
        unfold pieceTargets
        simp only [kingPiece, PieceType.King]
        have hNoCastleTrue : castleMoveIfLegal gs true = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM true
        have hNoCastleFalse : castleMoveIfLegal gs false = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM false
        simp only [hNoCastleTrue, hNoCastleFalse, List.filterMap_nil, List.append_nil]
        have hTarget : esc ∈ Movement.kingTargets wk := by
          rw [Movement.mem_kingTargets_iff]
          exact hEscAdj
        have hDestFree : destinationFriendlyFree gs { piece := kingPiece Color.White, fromSq := wk, toSq := esc } = true := by
          unfold destinationFriendlyFree
          cases hAt : gs.board esc with
          | none => rfl
          | some p =>
            have hEsc' : gs.board.get esc = some p := by simpa using hAt
            simp_all
        apply List.mem_filterMap.2
        refine ⟨esc, hTarget, ?_⟩
        simp only [hDestFree]
        cases hBoard : gs.board esc with
        | none => simp
        | some p =>
          have hEsc' : gs.board.get esc = some p := by simpa using hBoard
          simp_all
      · -- respectsPin
        unfold respectsPin
        cases hFind : (pinnedSquares gs gs.toMove).find? (fun p => p.fst = wk) with
        | none => rfl
        | some pinPair =>
          have ⟨_, hf, hr⟩ := hEscAdj
          by_cases hFd0 : Movement.absInt (Movement.fileDiff wk esc) = 0
          · simp [hFd0]
          · by_cases hRd0 : Movement.absInt (Movement.rankDiff wk esc) = 0
            · simp [hRd0]
            · have hFd1 : Movement.absInt (Movement.fileDiff wk esc) = 1 := by omega
              have hRd1 : Movement.absInt (Movement.rankDiff wk esc) = 1 := by omega
              simp [hFd1, hRd1]
      · -- basicLegalAndSafe
        unfold basicLegalAndSafe
        constructor
        · unfold basicMoveLegalBool
          have hOrigin : originHasPiece gs m = true := by
            unfold originHasPiece
            simp [hKPM.1]
          have hTurnM : turnMatches gs m = true := by
            unfold turnMatches
            simp [kingPiece, hTurn]
          have hDestFree : destinationFriendlyFree gs m = true := by
            unfold destinationFriendlyFree
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hCapFlag : captureFlagConsistent gs m = true := by
            unfold captureFlagConsistent
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hSqDiff : squaresDiffer m = true := by
            unfold squaresDiffer
            simp [hEscNeWk.symm]
          simp [hOrigin, hTurnM, hDestFree, hCapFlag, hSqDiff]
        · simp only [Bool.not_eq_true']
          have hBoard' : (gs.movePiece m).board =
              (gs.board.update wk none).update esc (some (kingPiece Color.White)) := by
            unfold GameState.movePiece
            simp [kingPiece]
          rw [hBoard', hTurn]
          have hNotAdjEscBk : ¬ Movement.isKingStep esc bk := by
            intro h
            exact hEscNotAdjBk (Movement.isKingStep_symm esc bk h)
          exact KingsPlusMinor_white_not_in_check_after_move_bishop
            hKPM hBishop hBishopBlack hEscNeWk hEscNeBk hEscNeMsq hEscEmpty
            hNotAdjEscBk hEscNotBishop
    have hNe : allLegalMoves gs ≠ [] := List.ne_nil_of_mem hMem
    exact List.isEmpty_eq_false_iff.mpr hNe
  | Black =>
    -- Black to move, in check from bishop
    have hChk : inCheck gs.board Color.Black = true := by simpa [inCheckStatus, hTurn] using hInCheck
    have ⟨hBishopWhite, hAtk⟩ := KingsPlusMinor.inCheck_black_implies_minor_attacker hKPM hNoAdj hChk
    have hBishopAttacksBk : msq ≠ bk ∧ Movement.isDiagonal msq bk := by
      unfold attacksSpec at hAtk
      simp only [hBishop] at hAtk
      have ⟨hDiag, hPath⟩ := hAtk
      exact ⟨hKPM.2.2.2.2.2.1.symm, hDiag⟩
    have hNoAdjBkWk : ¬ Movement.isKingStep bk wk := by
      intro h
      exact hNoAdj (Movement.isKingStep_symm bk wk h)
    obtain ⟨esc, hEscAdj, hEscNotAdjWk, hEscNotBishop⟩ :=
      Movement.exists_safe_escape_from_bishop bk wk msq hWkNeBk.symm hNoAdjBkWk hBishopAttacksBk
    let m : Move := { piece := kingPiece Color.Black, fromSq := bk, toSq := esc }
    have hEscNeBk : esc ≠ bk := hEscAdj.1.symm
    have hEscNeWk : esc ≠ wk := by
      intro hEq
      rw [hEq] at hEscAdj
      exact hNoAdjBkWk hEscAdj
    have hEscNeMsq : esc ≠ msq := by
      by_contra hEq
      rw [hEq] at hEscNeWk hEscNeBk
      have hEscEmpty := escape_square_empty_knight hKPM hEscNeWk hEscNeBk (by exact hEq)
      have hMsqOcc : gs.board.get msq = some mp := hKPM.2.2.1
      simp_all
    have hEscEmpty : gs.board.get esc = none :=
      escape_square_empty_knight hKPM hEscNeWk hEscNeBk hEscNeMsq
    have hMem : m ∈ allLegalMoves gs := by
      rw [mem_allLegalMoves_iff_encodedLegal]
      refine ⟨bk, kingPiece Color.Black, ?_, ?_, ?_, ?_, ?_⟩
      · exact hKPM.2.1
      · simp [kingPiece, hTurn]
      · unfold pieceTargets
        simp only [kingPiece, PieceType.King]
        have hNoCastleTrue : castleMoveIfLegal gs true = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM true
        have hNoCastleFalse : castleMoveIfLegal gs false = none :=
          KingsPlusMinor.castleMoveIfLegal_none (gs := gs) (wk := wk) (bk := bk) hKPM false
        simp only [hNoCastleTrue, hNoCastleFalse, List.filterMap_nil, List.append_nil]
        have hTarget : esc ∈ Movement.kingTargets bk := by
          rw [Movement.mem_kingTargets_iff]
          exact hEscAdj
        have hDestFree : destinationFriendlyFree gs { piece := kingPiece Color.Black, fromSq := bk, toSq := esc } = true := by
          unfold destinationFriendlyFree
          cases hAt : gs.board esc with
          | none => rfl
          | some p =>
            have hEsc' : gs.board.get esc = some p := by simpa using hAt
            simp_all
        apply List.mem_filterMap.2
        refine ⟨esc, hTarget, ?_⟩
        simp only [hDestFree]
        cases hBoard : gs.board esc with
        | none => simp
        | some p =>
          have hEsc' : gs.board.get esc = some p := by simpa using hBoard
          simp_all
      · unfold respectsPin
        cases hFind : (pinnedSquares gs gs.toMove).find? (fun p => p.fst = bk) with
        | none => rfl
        | some pinPair =>
          have ⟨_, hf, hr⟩ := hEscAdj
          by_cases hFd0 : Movement.absInt (Movement.fileDiff bk esc) = 0
          · simp [hFd0]
          · by_cases hRd0 : Movement.absInt (Movement.rankDiff bk esc) = 0
            · simp [hRd0]
            · have hFd1 : Movement.absInt (Movement.fileDiff bk esc) = 1 := by omega
              have hRd1 : Movement.absInt (Movement.rankDiff bk esc) = 1 := by omega
              simp [hFd1, hRd1]
      · unfold basicLegalAndSafe
        constructor
        · unfold basicMoveLegalBool
          have hOrigin : originHasPiece gs m = true := by
            unfold originHasPiece
            simp [hKPM.2.1]
          have hTurnM : turnMatches gs m = true := by
            unfold turnMatches
            simp [kingPiece, hTurn]
          have hDestFree : destinationFriendlyFree gs m = true := by
            unfold destinationFriendlyFree
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hCapFlag : captureFlagConsistent gs m = true := by
            unfold captureFlagConsistent
            cases hAt : gs.board esc with
            | none => rfl
            | some p =>
              have hEsc' : gs.board.get esc = some p := by simpa using hAt
              simp_all
          have hSqDiff : squaresDiffer m = true := by
            unfold squaresDiffer
            simp [hEscNeBk.symm]
          simp [hOrigin, hTurnM, hDestFree, hCapFlag, hSqDiff]
        · simp only [Bool.not_eq_true']
          have hBoard' : (gs.movePiece m).board =
              (gs.board.update bk none).update esc (some (kingPiece Color.Black)) := by
            unfold GameState.movePiece
            simp [kingPiece]
          rw [hBoard', hTurn]
          have hNotAdjWkEsc : ¬ Movement.isKingStep wk esc := by
            intro h
            exact hEscNotAdjWk (Movement.isKingStep_symm wk esc h)
          exact KingsPlusMinor_black_not_in_check_after_move_bishop
            hKPM hBishop hBishopWhite hEscNeWk hEscNeBk hEscNeMsq hEscEmpty
            hNotAdjWkEsc hEscNotBishop
    have hNe : allLegalMoves gs ≠ [] := List.ne_nil_of_mem hMem
    exact List.isEmpty_eq_false_iff.mpr hNe

/-- K+B vs K positions cannot be checkmate. -/
theorem KkbInv.isCheckmate_false (gs : GameState) :
    KkbInv gs → isCheckmate gs = false := by
  intro hInv
  rcases hInv with ⟨wk, bk, msq, mp, hKPM, hBishop, hNoAdj⟩
  unfold isCheckmate
  by_cases hChk : inCheckStatus gs = true
  · have hMoves : noLegalMoves gs = false :=
      bishop_check_has_escape gs wk bk msq mp hKPM hBishop hNoAdj hChk
    simp [hMoves]
  · simp [hChk]

/-- K+B or K vs K positions cannot be checkmate. -/
theorem KkbOrKkInv.isCheckmate_false (gs : GameState) :
    KkbOrKkInv gs → isCheckmate gs = false := by
  intro hInv
  rcases hInv with hKkb | hKk
  · exact KkbInv.isCheckmate_false gs hKkb
  · exact KkInv.isCheckmate_false gs hKk

/-- K+B or K vs K positions are dead positions. -/
theorem KkbOrKkInv.isDeadPosition (gs : GameState) :
    KkbOrKkInv gs → isDeadPosition gs := by
  intro hInv
  intro hContra
  rcases hContra with ⟨moves, gs', hOk, hMate⟩
  have hInv' : KkbOrKkInv gs' :=
    KkbOrKkInv.applyLegalMoves_preserved gs moves gs' hInv hOk
  have : isCheckmate gs' = false := KkbOrKkInv.isCheckmate_false gs' hInv'
  simp [this] at hMate

end Rules
end Chess
