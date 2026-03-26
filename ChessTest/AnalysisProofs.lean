import Chess.Analysis.Proofs
import Chess.Analysis.Equivalence
import Chess.Analysis.AlphaBetaDepth1Proofs
import Chess.Analysis.AlphaBetaDepth2Proofs
import Chess.Analysis.MinimaxBounds

open Chess
open Chess.Analysis

#check pvLegal
#check pvLegal_negamaxPV
#check pvLegal_negamaxPV_head
#check pvLength_negamaxPV
#check negamaxPV_value_ge_moveScore
#check negamaxPV_value_eq_headScore
#check negamaxPV_headScore_ge_moveScore
#check minimaxValue
#check negamaxPV_value_eq_minimaxValue
#check negamax_eq_minimaxValue
#check alphaBeta_depth1_eq_minimaxValue
#check alphaBeta_depth1_eq_negamax
#check alphaBeta_depth2_eq_minimaxValue
#check alphaBeta_depth2_eq_negamax
#check minimaxValue_bounds
