import Chess.KMinorUpdateLemmas

namespace Chess
namespace Rules

private theorem mem_allLegalMoves_implies_squaresDiffer
    (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs → squaresDiffer m = true := by
  intro hMem
  have hBasic : basicMoveLegalBool gs m = true :=
    mem_allLegalMoves_implies_basicMoveLegalBool gs m hMem
  have hConj :
      (((originHasPiece gs m = true ∧ turnMatches gs m = true) ∧
            destinationFriendlyFree gs m = true) ∧
          captureFlagConsistent gs m = true) ∧
        squaresDiffer m = true := by
    simpa [basicMoveLegalBool, Bool.and_eq_true] using hBasic
  exact hConj.2

theorem KingsPlusMinor.mem_allLegalMoves_destination_empty_or_minorSquare
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    gs.board.get m.toSq = none ∨ m.toSq = msq := by
  intro hKPM hMem
  cases hAt : gs.board.get m.toSq with
  | none =>
      left
      rfl
  | some p =>
      right
      -- Generated moves never target a king.
      have hNotKing : p.pieceType ≠ PieceType.King :=
        mem_allLegalMoves_implies_not_king_destination (gs := gs) (m := m) hMem p (by simpa [Board.get] using hAt)
      -- On a Kings+minor board, any occupied square is one of the three pieces.
      have hCases :=
        KingsPlusMinor.pieceType_cases (b := gs.board) (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM
          m.toSq p hAt
      rcases hCases with ⟨hp, hs⟩ | ⟨hp, hs⟩ | ⟨hp, hs⟩
      · cases hp
        cases (hNotKing (by simp [kingPiece]))
      · cases hp
        cases (hNotKing (by simp [kingPiece]))
      · exact hs

theorem KingsPlusMinor.whiteKing_captureMinor_yields_kingsOnly
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.piece = kingPiece Color.White →
    m.fromSq = wk →
    m.toSq = msq →
    KingsOnly (gs.movePiece m).board msq bk := by
  intro hKPM hMem hPiece hFrom hTo
  have hBoard :
      (gs.movePiece m).board =
        (gs.board.update m.fromSq none).update m.toSq (some m.piece) :=
    KingsPlusMinor.movePiece_board_eq_update_update (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  -- Normalize the update squares using the hypotheses.
  have hWkNeBk : wk ≠ bk := hKPM.2.2.2.2.1
  have hWkNeMsq : wk ≠ msq := hKPM.2.2.2.2.2.1
  have hBkNeMsq : bk ≠ msq := hKPM.2.2.2.2.2.2.1
  -- Build `KingsOnly` by reading the updated board.
  unfold KingsOnly
  -- Define the post-move board.
  let b' : Board := (gs.board.update wk none).update msq (some (kingPiece Color.White))
  have hBoard' : (gs.movePiece m).board = b' := by
    simpa [b', hFrom, hTo, hPiece] using hBoard
  -- Now prove the four fields of `KingsOnly` (nested `∧`).
  refine ⟨?_, ?_⟩
  · -- White king at `msq`
    simp [hBoard', b', Board.update_eq]
  · refine ⟨?_, ?_⟩
    · -- Black king at `bk`
      have hBkNeMsq' : bk ≠ msq := by simpa using hBkNeMsq
      have hBkNeWk' : bk ≠ wk := by simpa using hWkNeBk.symm
      have hAtBk : gs.board.get bk = some (kingPiece Color.Black) := hKPM.2.1
      simp [hBoard', b', Board.update_ne _ _ _ hBkNeMsq', Board.update_ne _ _ _ hBkNeWk', hAtBk]
    · refine ⟨?_, ?_⟩
      · -- distinct king squares
        exact hBkNeMsq.symm
      · -- all other squares empty
        intro sq hNeW hNeB
        by_cases hSqWk : sq = wk
        · cases hSqWk
          have hWkNeMsq' : wk ≠ msq := by simpa using hWkNeMsq
          simp [hBoard', b', Board.update_ne _ _ _ hWkNeMsq', Board.update_eq]
        · have hNeMsq : sq ≠ msq := by simpa using hNeW
          have hNeBk : sq ≠ bk := hNeB
          have hStart : gs.board.get sq = none := by
            exact hKPM.2.2.2.2.2.2.2 sq hSqWk hNeBk hNeMsq
          simp [hBoard', b', Board.update_ne _ _ _ hNeMsq, Board.update_ne _ _ _ hSqWk, hStart]

theorem KingsPlusMinor.blackKing_captureMinor_yields_kingsOnly
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    m.piece = kingPiece Color.Black →
    m.fromSq = bk →
    m.toSq = msq →
    KingsOnly (gs.movePiece m).board wk msq := by
  intro hKPM hMem hPiece hFrom hTo
  have hBoard :
      (gs.movePiece m).board =
        (gs.board.update m.fromSq none).update m.toSq (some m.piece) :=
    KingsPlusMinor.movePiece_board_eq_update_update (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hWkNeBk : wk ≠ bk := hKPM.2.2.2.2.1
  have hWkNeMsq : wk ≠ msq := hKPM.2.2.2.2.2.1
  have hBkNeMsq : bk ≠ msq := hKPM.2.2.2.2.2.2.1
  let b' : Board := (gs.board.update bk none).update msq (some (kingPiece Color.Black))
  have hBoard' : (gs.movePiece m).board = b' := by
    simpa [b', hFrom, hTo, hPiece] using hBoard
  unfold KingsOnly
  refine ⟨?_, ?_⟩
  · -- White king at `wk` (untouched by the updates)
    have hWkNeMsq' : wk ≠ msq := by simpa using hWkNeMsq
    have hWkNeBk' : wk ≠ bk := by simpa using hWkNeBk
    have hAtWk : gs.board.get wk = some (kingPiece Color.White) := hKPM.1
    simp [hBoard', b', Board.update_ne _ _ _ hWkNeMsq', Board.update_ne _ _ _ hWkNeBk', hAtWk]
  · refine ⟨?_, ?_⟩
    · -- Black king at `msq`
      simp [hBoard', b', Board.update_eq]
    · refine ⟨?_, ?_⟩
      · -- distinct king squares
        exact hWkNeMsq
      · -- all other squares empty
        intro sq hNeW hNeB
        by_cases hSqBk : sq = bk
        · cases hSqBk
          have hBkNeMsq' : bk ≠ msq := by simpa using hBkNeMsq
          simp [hBoard', b', Board.update_ne _ _ _ hBkNeMsq', Board.update_eq]
        · have hNeMsq : sq ≠ msq := hNeB
          have hNeWk : sq ≠ wk := hNeW
          have hStart : gs.board.get sq = none := by
            exact hKPM.2.2.2.2.2.2.2 sq hNeWk hSqBk hNeMsq
          simp [hBoard', b', Board.update_ne _ _ _ hNeMsq, Board.update_ne _ _ _ hSqBk, hStart]

end Rules
end Chess
