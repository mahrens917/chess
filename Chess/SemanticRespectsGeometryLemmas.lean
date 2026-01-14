import Chess.Spec
import Chess.SemanticGeometryLemmas
import Chess.SemanticSlidingRespectsGeometryLemmas
import Chess.SemanticPawnTargetsGeometryLemmas

namespace Chess
namespace Rules

theorem respectsGeometry_of_pieceTargets
    (gs : GameState) (src : Square) (p : Piece) (m : Move) :
    m ∈ pieceTargets gs src p →
    respectsGeometry gs m := by
  intro hMem
  cases hPt : p.pieceType with
  | King =>
      by_cases hCastle : m.isCastle = true
      ·
        have hKing : p.pieceType = PieceType.King := by simp [hPt]
        exact respectsGeometry_of_pieceTargets_king_castle gs src p m hKing hMem hCastle
      ·
        have hKing : p.pieceType = PieceType.King := by simp [hPt]
        -- Normalize `m.isCastle = false` for the lemma.
        have hNoCastle : m.isCastle = false := by
          cases hIs : m.isCastle with
          | false => simpa using hIs
          | true => cases (hCastle hIs)
        exact respectsGeometry_of_pieceTargets_king_not_castle gs src p m hKing hMem hNoCastle
  | Queen =>
      have hQueen : p.pieceType = PieceType.Queen := by simp [hPt]
      exact respectsGeometry_of_pieceTargets_queen gs src p m hQueen hMem
  | Rook =>
      have hRook : p.pieceType = PieceType.Rook := by simp [hPt]
      exact respectsGeometry_of_pieceTargets_rook gs src p m hRook hMem
  | Bishop =>
      have hBishop : p.pieceType = PieceType.Bishop := by simp [hPt]
      exact respectsGeometry_of_pieceTargets_bishop gs src p m hBishop hMem
  | Knight =>
      have hKnight : p.pieceType = PieceType.Knight := by simp [hPt]
      exact respectsGeometry_of_pieceTargets_knight gs src p m hKnight hMem
  | Pawn =>
      have hPawn : p.pieceType = PieceType.Pawn := by simp [hPt]
      exact respectsGeometry_of_pieceTargets_pawn gs src p m hPawn hMem

end Rules
end Chess

