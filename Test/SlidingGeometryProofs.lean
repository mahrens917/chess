import Chess.SemanticSlidingGeometryLemmas
import Chess.SemanticSlidingRespectsGeometryLemmas

open Chess Chess.Rules

-- Verify sliding-geometry lemmas are accessible and type-check.

#check isRookDelta
#check isBishopDelta
#check isQueenDelta

#check mem_slidingTargets_isRookMove
#check mem_slidingTargets_isDiagonal
#check mem_slidingTargets_isQueenMove

#check mem_pieceTargets_rook_isRookMove
#check mem_pieceTargets_bishop_isDiagonal
#check mem_pieceTargets_queen_isQueenMove

#check respectsGeometry_of_pieceTargets_rook
#check respectsGeometry_of_pieceTargets_bishop
#check respectsGeometry_of_pieceTargets_queen
