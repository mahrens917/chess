import Chess.EndConditionsSpec

open Chess Chess.Rules

-- Verify end-condition specs are accessible and type-check.

#check noLegalMovesSpec
#check inCheckStatusSpec
#check isCheckmateSpec
#check isStalemateSpec

#check noLegalMoves_iff_noLegalMovesSpec
#check inCheckStatus_iff_inCheckStatusSpec
#check isCheckmate_iff_isCheckmateSpec
#check isStalemate_iff_isStalemateSpec

