import Chess.HistorySpec

open Chess Chess.Rules

-- Verify history/repetition spec lemmas are accessible and type-check.

#check finalizeResult_history
#check GameState.playMove_history
#check threefoldRepetition_eq_count
#check fivefoldRepetition_eq_count

