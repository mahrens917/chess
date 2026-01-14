import Chess.KMinorCaptureLemmas

namespace Chess
namespace Rules

private theorem mem_allLegalMoves_implies_captureFlagConsistent
    (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs → captureFlagConsistent gs m = true := by
  intro hMem
  have hBasic : basicMoveLegalBool gs m = true :=
    mem_allLegalMoves_implies_basicMoveLegalBool gs m hMem
  have hConj :
      (((originHasPiece gs m = true ∧ turnMatches gs m = true) ∧
            destinationFriendlyFree gs m = true) ∧
          captureFlagConsistent gs m = true) ∧
        squaresDiffer m = true := by
    simpa [basicMoveLegalBool, Bool.and_eq_true] using hBasic
  exact hConj.1.2

theorem KingsPlusMinor.mem_allLegalMoves_isCapture_false_implies_toSq_empty
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.isCapture = false →
    gs.board.get m.toSq = none := by
  intro hKPM hMem hCapFalse
  have hCapCons : captureFlagConsistent gs m = true :=
    mem_allLegalMoves_implies_captureFlagConsistent (gs := gs) (m := m) hMem
  have hEP : m.isEnPassant = false :=
    KingsPlusMinor.mem_allLegalMoves_isEnPassant_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  unfold captureFlagConsistent at hCapCons
  simp [hEP] at hCapCons
  cases hAt : gs.board.get m.toSq with
  | none =>
      rfl
  | some p =>
      have : m.isCapture = true := by
        simpa [hAt] using hCapCons
      have : (false : Bool) = true := by
        simpa [hCapFalse] using this
      cases this

theorem KingsPlusMinor.mem_allLegalMoves_isCapture_false_preserves
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.isCapture = false →
    (m.piece = kingPiece Color.White ∧
        KingsPlusMinor (gs.movePiece m).board m.toSq bk msq mp) ∨
      (m.piece = kingPiece Color.Black ∧
        KingsPlusMinor (gs.movePiece m).board wk m.toSq msq mp) ∨
      (m.piece = mp ∧
        KingsPlusMinor (gs.movePiece m).board wk bk m.toSq mp) := by
  intro hKPM hMem hCapFalse
  have hToEmpty : gs.board.get m.toSq = none :=
    KingsPlusMinor.mem_allLegalMoves_isCapture_false_implies_toSq_empty
      (gs := gs) (m := m) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem hCapFalse
  have hBoard :
      (gs.movePiece m).board =
        (gs.board.update m.fromSq none).update m.toSq (some m.piece) :=
    KingsPlusMinor.movePiece_board_eq_update_update (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hNotKingDest : ∀ p, gs.board.get m.toSq = some p → p.pieceType ≠ PieceType.King :=
    mem_allLegalMoves_implies_not_king_destination (gs := gs) (m := m) hMem
  have hPieceCases :
      m.piece = kingPiece Color.White ∨ m.piece = kingPiece Color.Black ∨ m.piece = mp :=
    KingsPlusMinor.mem_allLegalMoves_piece_cases (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hWkNeBk : wk ≠ bk := hKPM.2.2.2.2.1
  have hWkNeMsq : wk ≠ msq := hKPM.2.2.2.2.2.1
  have hBkNeMsq : bk ≠ msq := hKPM.2.2.2.2.2.2.1
  have hAtWk : gs.board.get wk = some (kingPiece Color.White) := hKPM.1
  have hAtBk : gs.board.get bk = some (kingPiece Color.Black) := hKPM.2.1
  have hAtMsq : gs.board.get msq = some mp := hKPM.2.2.1

  -- `toSq` cannot be `wk`, `bk`, or `msq` in the non-capture case.
  have hToNeWk : m.toSq ≠ wk := by
    intro hEq
    have : gs.board.get m.toSq = some (kingPiece Color.White) := by simpa [hEq] using hAtWk
    cases (hNotKingDest (kingPiece Color.White) this) (by simp [kingPiece])
  have hToNeBk : m.toSq ≠ bk := by
    intro hEq
    have : gs.board.get m.toSq = some (kingPiece Color.Black) := by simpa [hEq] using hAtBk
    cases (hNotKingDest (kingPiece Color.Black) this) (by simp [kingPiece])
  have hToNeMsq : m.toSq ≠ msq := by
    intro hEq
    have : gs.board.get m.toSq = some mp := by simpa [hEq] using hAtMsq
    have : (none : Option Piece) = some mp := by
      simpa [hToEmpty] using this
    cases this

  rcases hPieceCases with hW | hB | hM
  · left
    refine ⟨hW, ?_⟩
    have hFrom : m.fromSq = wk :=
      KingsPlusMinor.mem_allLegalMoves_fromSq_eq_wk_of_piece_whiteKing (gs := gs) (m := m)
        (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem hW
    -- Construct the new KingsPlusMinor on the updated board.
    have hBoard' : (gs.movePiece m).board =
        (gs.board.update wk none).update m.toSq (some (kingPiece Color.White)) := by
      simp [hBoard, hFrom, hW]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- white king at new square
      simp [hBoard', Board.update_eq]
    · -- black king stays at bk
      have hBkNeTo : bk ≠ m.toSq := by symm; exact hToNeBk
      have hBkNeWk' : bk ≠ wk := by symm; exact hWkNeBk
      simp [hBoard', Board.update_ne _ _ _ hBkNeTo, Board.update_ne _ _ _ hBkNeWk', hAtBk]
    · -- minor stays at msq
      have hMsqNeTo : msq ≠ m.toSq := by symm; exact hToNeMsq
      have hMsqNeWk' : msq ≠ wk := by symm; exact hWkNeMsq
      simp [hBoard', Board.update_ne _ _ _ hMsqNeTo, Board.update_ne _ _ _ hMsqNeWk', hAtMsq]
    · -- minor is still minor
      exact hKPM.2.2.2.1
    · -- king squares distinct
      exact hToNeBk
    · -- new wk ≠ msq
      exact hToNeMsq
    · -- bk ≠ msq (unchanged)
      exact hBkNeMsq
    · intro sq hNeW hNeB hNeM
      -- Reduce to original emptiness using update-neq reasoning.
      by_cases hSqWk : sq = wk
      · cases hSqWk
        -- wk cleared; also wk ≠ toSq.
        simp [hBoard', Board.update_ne _ _ _ (by symm; exact hToNeWk), Board.update_eq]
      · have hNeTo : sq ≠ m.toSq := by
          intro hEq
          exact hNeW (by simpa [hEq] using rfl)
        have hStart : gs.board.get sq = none := hKPM.2.2.2.2.2.2.2 sq hSqWk (by
          intro hEq
          subst hEq
          exact hNeB rfl) (by
          intro hEq
          subst hEq
          exact hNeM rfl)
        simp [hBoard', Board.update_ne _ _ _ hNeTo, Board.update_ne _ _ _ hSqWk, hStart]
  · right; left
    refine ⟨hB, ?_⟩
    have hFrom : m.fromSq = bk :=
      KingsPlusMinor.mem_allLegalMoves_fromSq_eq_bk_of_piece_blackKing (gs := gs) (m := m)
        (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem hB
    have hBoard' : (gs.movePiece m).board =
        (gs.board.update bk none).update m.toSq (some (kingPiece Color.Black)) := by
      simp [hBoard, hFrom, hB]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- white king stays
      have hWkNeTo : wk ≠ m.toSq := by symm; exact hToNeWk
      have hWkNeBk' : wk ≠ bk := hWkNeBk
      simp [hBoard', Board.update_ne _ _ _ hWkNeTo, Board.update_ne _ _ _ hWkNeBk', hAtWk]
    · -- black king at new square
      simp [hBoard', Board.update_eq]
    · -- minor stays
      have hMsqNeTo : msq ≠ m.toSq := by symm; exact hToNeMsq
      have hMsqNeBk' : msq ≠ bk := by symm; exact hBkNeMsq
      simp [hBoard', Board.update_ne _ _ _ hMsqNeTo, Board.update_ne _ _ _ hMsqNeBk', hAtMsq]
    · exact hKPM.2.2.2.1
    · -- wk ≠ new bk
      exact Ne.symm hToNeWk
    · -- wk ≠ msq
      exact hWkNeMsq
    · -- new bk ≠ msq
      exact hToNeMsq
    · intro sq hNeW hNeB hNeM
      by_cases hSqBk : sq = bk
      · cases hSqBk
        simp [hBoard', Board.update_ne _ _ _ (by symm; exact hToNeBk), Board.update_eq]
      · have hNeTo : sq ≠ m.toSq := by
          intro hEq
          exact hNeB (by simpa [hEq] using rfl)
        have hStart : gs.board.get sq = none := hKPM.2.2.2.2.2.2.2 sq (by
          intro hEq
          subst hEq
          exact hNeW rfl) hSqBk (by
          intro hEq
          subst hEq
          exact hNeM rfl)
        simp [hBoard', Board.update_ne _ _ _ hNeTo, Board.update_ne _ _ _ hSqBk, hStart]
  · right; right
    refine ⟨hM, ?_⟩
    have hFrom : m.fromSq = msq :=
      KingsPlusMinor.mem_allLegalMoves_fromSq_eq_msq_of_piece_minor (gs := gs) (m := m)
        (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem hM
    have hBoard' : (gs.movePiece m).board =
        (gs.board.update msq none).update m.toSq (some mp) := by
      simp [hBoard, hFrom, hM]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- white king stays
      have hWkNeTo : wk ≠ m.toSq := by symm; exact hToNeWk
      have hWkNeMsq' : wk ≠ msq := hWkNeMsq
      simp [hBoard', Board.update_ne _ _ _ hWkNeTo, Board.update_ne _ _ _ hWkNeMsq', hAtWk]
    · -- black king stays
      have hBkNeTo : bk ≠ m.toSq := by symm; exact hToNeBk
      have hBkNeMsq' : bk ≠ msq := hBkNeMsq
      simp [hBoard', Board.update_ne _ _ _ hBkNeTo, Board.update_ne _ _ _ hBkNeMsq', hAtBk]
    · -- minor moved to new square
      simp [hBoard', Board.update_eq]
    · exact hKPM.2.2.2.1
    · exact hWkNeBk
    · exact Ne.symm hToNeWk
    · exact Ne.symm hToNeBk
    · intro sq hNeW hNeB hNeM
      by_cases hSqMsq : sq = msq
      · cases hSqMsq
        simp [hBoard', Board.update_ne _ _ _ (by symm; exact hToNeMsq), Board.update_eq]
      · have hNeTo : sq ≠ m.toSq := by
          intro hEq
          exact hNeM (by simpa [hEq] using rfl)
        have hStart : gs.board.get sq = none := hKPM.2.2.2.2.2.2.2 sq (by
          intro hEq
          subst hEq
          exact hNeW rfl) (by
          intro hEq
          subst hEq
          exact hNeB rfl) hSqMsq
        simp [hBoard', Board.update_ne _ _ _ hNeTo, Board.update_ne _ _ _ hSqMsq, hStart]

end Rules
end Chess
