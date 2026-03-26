import Chess.MaterialSpec

open Chess Chess.Rules

-- Verify material/draw spec predicates are accessible and type-check.

#check insufficientMaterialExact
#check deadPositionHeuristic

#check insufficientMaterial_eq_true_iff
#check deadPosition_eq_true_iff

