import Chess.AttackSpec

open Chess Chess.Rules

-- Verify attack/check bridge theorems are accessible and type-check.

#check attacksSpec
#check pieceAttacksSquare_eq_true_iff_attacksSpec
#check anyAttacksSquare_eq_true_iff_exists_attacker
#check inCheck_eq_true_iff_exists_attacker

