import Chess.Spec
import Chess.ParsingProofs
import Chess.SemanticSlidingGeometryLemmas
import Chess.SemanticSlidingPathClearLemmas

namespace Chess
namespace Rules

theorem respectsGeometry_of_pieceTargets_rook
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hRook : p.pieceType = PieceType.Rook) :
    m ∈ pieceTargets gs src p →
    respectsGeometry gs m := by
  intro hMem
  have hMove : Movement.isRookMove src m.toSq :=
    mem_pieceTargets_rook_isRookMove gs src p m hRook hMem
  have hPC : Rules.pathClear gs.board src m.toSq = true :=
    mem_pieceTargets_rook_pathClear gs src p m hRook hMem
  have hMem' :
      m ∈
        slidingTargets gs src p [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
    simpa [pieceTargets, hRook] using hMem
  have hPieceFrom := Chess.Parsing.mem_slidingTargets_piece_fromSq gs src p
    [(1, 0), (-1, 0), (0, 1), (0, -1)] m hMem'
  rcases hPieceFrom with ⟨hPiece, hFrom⟩
  subst hPiece
  subst hFrom
  simp [respectsGeometry, hRook, hMove, hPC]

theorem respectsGeometry_of_pieceTargets_bishop
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hBishop : p.pieceType = PieceType.Bishop) :
    m ∈ pieceTargets gs src p →
    respectsGeometry gs m := by
  intro hMem
  have hMove : Movement.isDiagonal src m.toSq :=
    mem_pieceTargets_bishop_isDiagonal gs src p m hBishop hMem
  have hPC : Rules.pathClear gs.board src m.toSq = true :=
    mem_pieceTargets_bishop_pathClear gs src p m hBishop hMem
  have hMem' :
      m ∈
        slidingTargets gs src p [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
    simpa [pieceTargets, hBishop] using hMem
  have hPieceFrom := Chess.Parsing.mem_slidingTargets_piece_fromSq gs src p
    [(1, 1), (-1, -1), (1, -1), (-1, 1)] m hMem'
  rcases hPieceFrom with ⟨hPiece, hFrom⟩
  subst hPiece
  subst hFrom
  simp [respectsGeometry, hBishop, hMove, hPC]

theorem respectsGeometry_of_pieceTargets_queen
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hQueen : p.pieceType = PieceType.Queen) :
    m ∈ pieceTargets gs src p →
    respectsGeometry gs m := by
  intro hMem
  have hMove : Movement.isQueenMove src m.toSq :=
    mem_pieceTargets_queen_isQueenMove gs src p m hQueen hMem
  have hPC : Rules.pathClear gs.board src m.toSq = true :=
    mem_pieceTargets_queen_pathClear gs src p m hQueen hMem
  have hMem' :
      m ∈
        slidingTargets gs src p
          [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)] := by
    simpa [pieceTargets, hQueen] using hMem
  have hPieceFrom := Chess.Parsing.mem_slidingTargets_piece_fromSq gs src p
    [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)] m hMem'
  rcases hPieceFrom with ⟨hPiece, hFrom⟩
  subst hPiece
  subst hFrom
  simp [respectsGeometry, hQueen, hMove, hPC]

end Rules
end Chess

