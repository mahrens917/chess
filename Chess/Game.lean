import Chess.Core

namespace Chess

def GameState.movePiece (gs : GameState) (m : Move) : GameState :=
  let board' := (gs.board.update m.fromSq none).update m.toSq (some m.piece)
  let resetHalf := m.isCapture || m.piece.pieceType == PieceType.Pawn
  let nextFull := if gs.toMove = Color.Black then gs.fullMoveNumber + 1 else gs.fullMoveNumber
  { gs with
    board := board'
    toMove := gs.toMove.opposite
    halfMoveClock := if resetHalf then 0 else gs.halfMoveClock + 1
    fullMoveNumber := nextFull
  }

namespace Game

theorem movePiece_flips_turn (gs : GameState) (m : Move) :
    (gs.movePiece m).toMove = gs.toMove.opposite := by
  simp [GameState.movePiece]

theorem movePiece_halfmove (gs : GameState) (m : Move) :
    (gs.movePiece m).halfMoveClock =
      if m.isCapture || m.piece.pieceType == PieceType.Pawn then 0 else gs.halfMoveClock + 1 := by
  simp [GameState.movePiece]

theorem movePiece_fullmove (gs : GameState) (m : Move) :
    (gs.movePiece m).fullMoveNumber =
      if gs.toMove = Color.Black then gs.fullMoveNumber + 1 else gs.fullMoveNumber := by
  simp [GameState.movePiece]

theorem movePiece_clears_source {gs : GameState} {m : Move} (h : m.fromSq ≠ m.toSq) :
    (gs.movePiece m).board m.fromSq = none := by
  simp [GameState.movePiece]
  have h1 :=
    Board.update_ne (gs.board.update m.fromSq none) m.toSq (some m.piece) (target := m.fromSq) h
  have h2 := Board.update_eq gs.board m.fromSq none
  simp [h1, h2]

theorem movePiece_sets_destination (gs : GameState) (m : Move) :
    (gs.movePiece m).board m.toSq = some m.piece := by
  simp [GameState.movePiece]
  exact Board.update_eq (gs.board.update m.fromSq none) m.toSq (some m.piece)

theorem movePiece_preserves_other {gs : GameState} {m : Move} {target : Square}
    (hfrom : target ≠ m.fromSq) (hto : target ≠ m.toSq) :
    (gs.movePiece m).board target = gs.board target := by
  simp [GameState.movePiece]
  have h1 := Board.update_ne gs.board m.fromSq none (target := target) hfrom
  have h2 := Board.update_ne (gs.board.update m.fromSq none) m.toSq (some m.piece)
    (target := target) hto
  simp [h1, h2]

end Game

end Chess
