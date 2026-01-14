import Chess.KMinorMoveLemmas

namespace Chess
namespace Rules

theorem KingsPlusMinor.movePiece_board_eq_update_update
    (gs : GameState) (m : Move) {wk bk msq : Square} {mp : Piece} :
    KingsPlusMinor gs.board wk bk msq mp →
    m ∈ allLegalMoves gs →
    (gs.movePiece m).board =
      (gs.board.update m.fromSq none).update m.toSq (some m.piece) := by
  intro hKPM hMem
  have hCastle : m.isCastle = false :=
    KingsPlusMinor.mem_allLegalMoves_isCastle_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hEP : m.isEnPassant = false :=
    KingsPlusMinor.mem_allLegalMoves_isEnPassant_false (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  have hPromo : m.promotion = none :=
    KingsPlusMinor.mem_allLegalMoves_promotion_none (gs := gs) (m := m)
      (wk := wk) (bk := bk) (msq := msq) (mp := mp) hKPM hMem
  -- With no EP/castling/promotion, `movePiece` is just an update+update.
  unfold GameState.movePiece
  simp [GameState.promotedPiece, enPassantCaptureSquare, hEP, hCastle, hPromo]

end Rules
end Chess

