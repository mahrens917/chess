import Chess.SemanticSlidingPathClearLemmas

open Chess Chess.Rules

-- Verify sliding path-clear lemmas are accessible and type-check.

#check rayEmptyUpTo

#check pathClear_of_rayEmptyUpTo_rookDelta
#check pathClear_of_rayEmptyUpTo_bishopDelta

#check slidingTargets_walk_mem_pathClear
#check mem_slidingTargets_pathClear

#check mem_pieceTargets_rook_pathClear
#check mem_pieceTargets_bishop_pathClear
#check mem_pieceTargets_queen_pathClear

