import Chess.SemanticPawnLemmas
import Chess.SemanticPawnTargetsGeometryLemmas

open Chess Chess.Rules

-- Verify pawn semantic lemmas are accessible and type-check.

#check pawnDirection_ne_zero
#check isPawnAdvance_of_oneStep
#check isPawnAdvance_of_twoStep
#check isPawnCapture_of_step

#check promotionMoves_mem_preserves_squares

#check respectsGeometry_of_pieceTargets_pawn
