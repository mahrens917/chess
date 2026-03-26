import Chess.Spec
import Chess.RulesComplete
import Chess.PerftProofs
import Chess.StateInvariants
import Chess.SemanticFideLegalEquivalenceReachable
import Chess.ApplyLegalMovesLemmas
import Chess.ParsingRoundtripProofs
import Chess.ParsingFieldRoundtripProofs
import Chess.ParsingSANRoundtripProofs
import Chess.ParsingSANFixtureProofs
import Chess.ParsingPlacementFixtureProofs
import Chess.ParsingPlacementRoundtripProofs
import Chess.ParsingCharRoundtripProofs
import Chess.ParsingPlacementNoSlashProofs
import Chess.ParsingPlacementRankNoSlashProofs
import Chess.ParsingPlacementRankParsingLemmas
import Chess.ParsingPlacementRankStepLemmas
import Chess.ParsingPlacementGeneralRoundtripProofs
import Chess.ParsingFENSplitProofs
import Chess.ParsingFENGeneralRoundtripProofs
import Chess.BoardRoundtripProofs
import Chess.DeadPositionProofs
import Chess.KkDeadPositionProofs
import Chess.KMinorBoard
import Chess.KMinorMoveLemmas
import Chess.KMinorUpdateLemmas
import Chess.KMinorTransitionLemmas
import Chess.KMinorSourceLemmas
import Chess.KMinorCaptureLemmas
import Chess.KMinorPreservationLemmas
import Chess.KMinorDeadPositionInvariants
import Chess.KMinorSpecificEndgameInvariants
import Chess.Analysis.Equivalence
import Chess.Analysis.AlphaBetaDepth1Proofs
import Chess.Analysis.AlphaBetaDepth2Proofs
import Chess.Analysis.AlphaBetaWindow
import Chess.Analysis.AlphaBetaListLemmas
import Chess.Analysis.TerminalValueDeadPositionProofs
import Chess.Analysis.TerminalValueLemmas

open Chess
open Chess.Analysis

-- Rules-complete move generator spec surface.
#check Chess.Rules.allLegalMoves_iff_fideLegal
#check Chess.Rules.mem_allLegalMoves_iff_encodedLegal

-- Semantic ↔ generator equivalence for reachable states.
#check Chess.Rules.reachableFromStandard
#check Chess.Rules.fideLegalSemantic_iff_mem_allLegalMoves_of_reachable

-- `playMove` / invariant hooks used by the reachable-state story.
#check Chess.Rules.hasValidEPRank_playMove_of_mem_allLegalMoves
#check Chess.Rules.reachableFromStandard_hasValidEPRank

-- Structural sanity: generated moves never capture kings.
#check Chess.Rules.mem_allLegalMoves_implies_destinationFriendlyFree
#check Chess.Rules.mem_allLegalMoves_implies_not_king_destination

-- Perft correctness.
#check Chess.Rules.perft_correct

-- Dead position is treated as an auto draw (Rules layer).
#check Chess.Rules.drawStatus_autoDraw_of_deadPosition
#check Chess.Rules.interpretResult_of_deadPosition
#check Chess.Rules.finalizeResult_sets_draw_of_deadPosition
#check Chess.Rules.finalizeResult_sets_draw_of_insufficientMaterial
#check Chess.Rules.GameState.playMove_sets_draw_of_deadPosition
#check Chess.Rules.GameState.playMove_sets_draw_of_insufficientMaterial
#check Chess.Rules.isDeadPosition_implies_not_checkmate
#check Chess.Rules.applyLegalMoves_nil
#check Chess.Rules.applyLegalMoves_cons
#check Chess.Rules.applyLegalMoves_eq_ok_cons_iff
#check Chess.Rules.KkInv.isDeadPosition
#check Chess.Rules.isDeadPosition_of_KingsOnly
#check Chess.Rules.isDeadPosition_kkGameState
#check Chess.Rules.KingsPlusMinor.castleMoveIfLegal_none
#check Chess.Rules.KingsPlusMinor.inCheck_white_implies_minor_attacker
#check Chess.Rules.KingsPlusMinor.inCheck_black_implies_minor_attacker
#check Chess.Rules.KingsPlusMinor.inCheck_white_of_isKingStep
#check Chess.Rules.KingsPlusMinor.inCheck_black_of_isKingStep
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_isCastle_false
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_fromSq
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_piece_cases
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_isEnPassant_false
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_promotion_none
#check Chess.Rules.KingsPlusMinor.movePiece_board_eq_update_update
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_destination_empty_or_minorSquare
#check Chess.Rules.KingsPlusMinor.whiteKing_captureMinor_yields_kingsOnly
#check Chess.Rules.KingsPlusMinor.blackKing_captureMinor_yields_kingsOnly
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_fromSq_eq_wk_of_piece_whiteKing
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_fromSq_eq_bk_of_piece_blackKing
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_fromSq_eq_msq_of_piece_minor
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_isCapture_implies_toSq_minorSquare
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_isCapture_implies_piece_is_opponentKing
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_isCapture_implies_fromSq_opponentKingSquare
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_isCapture_false_implies_toSq_empty
#check Chess.Rules.KingsPlusMinor.mem_allLegalMoves_isCapture_false_preserves
#check Chess.Rules.KMinorInv.applyLegalMove_preserved_or_kkInv
#check Chess.Rules.KMinorOrKkInv.applyLegalMoves_preserved
#check Chess.Rules.KknInv.applyLegalMove_preserved_or_kkInv
#check Chess.Rules.KkbInv.applyLegalMove_preserved_or_kkInv
#check Chess.Rules.KknOrKkInv.applyLegalMoves_preserved
#check Chess.Rules.KkbOrKkInv.applyLegalMoves_preserved

-- Minimal FEN serialization sanity (start position is canonical).
#check Chess.Parsing.toFEN_buildStartingState_eq_startFEN
#check Chess.Parsing.parseFEN_toFEN_buildStartingState

-- FEN field roundtrips.
#check Chess.Parsing.parseActiveColor_roundtrip
#check Chess.Parsing.parseCastlingRights_roundtrip
#check Chess.Parsing.parseEnPassant_dash_roundtrip
#check Chess.Parsing.parseEnPassant_algebraic_roundtrip

-- FEN field splitting for `toFEN`.
#check Chess.Parsing.splitFenFields_toFEN

-- Full-FEN roundtrip (under `validateFEN`).
#check Chess.Parsing.parseFEN_toFEN_of_validate_of_split

-- Nat-field parsing roundtrip for `toString`.
#check Chess.Parsing.parseNatField_toString_roundtrip

-- Placement roundtrip (fixture): `Board` ↔ placement.
#check Chess.Parsing.parsePlacement_boardToFenPlacement_startingBoard

-- Board reconstruction (core prerequisite for general placement roundtrip).
#check Chess.Board.fromList_toList
#check Chess.Board.fromList_get_eq_none_of_forall_ne
#check Chess.Board.fromList_get_eq_some_of_mem_unique

-- Placement splitting/joining (proof-friendly replacement for `String.splitOn`/`intercalate`).
#check Chess.Parsing.splitPlacementChars_joinPlacementChars

-- Basic character encodings used by placement proofs.
#check Chess.Parsing.pieceFromChar_pieceToChar
#check Chess.Parsing.fenDigitValue?_digitChar_succ
#check Chess.Parsing.fenDigitValue?_digitChar

-- Characters emitted by placement printing are never rank separators.
#check Chess.Parsing.pieceToChar_ne_slash
#check Chess.Parsing.digitChar_ne_slash_of_le8

-- Rank placement output never contains '/' and splits back into ranks.
#check Chess.Parsing.rankToFenChars_no_slash
#check Chess.Parsing.splitPlacementChars_boardToFenPlacement

-- One-step rank parsing helpers (for the general placement roundtrip).
#check Chess.Parsing.parsePlacementRankChars_pieceToChar
#check Chess.Parsing.parsePlacementRankChars_digitChar_succ
#check Chess.Parsing.parsePlacementRankChars_digitChar

-- One-step rank printing helpers (for the general placement roundtrip).
#check Chess.Parsing.rankToFenCharsAux_step_none
#check Chess.Parsing.rankToFenCharsAux_step_some
#check Chess.Parsing.rankToFenCharsAux_done

-- General placement roundtrip.
#check Chess.Parsing.parsePlacement_boardToFenPlacement_roundtrip

-- Minimal SAN sanity (start position).
#check Chess.Parsing.moveFromSAN_start_e4
#check Chess.Parsing.applySAN_start_e4_toFEN

-- SAN fixtures (en passant / castling / promotion).
#check Chess.Parsing.fenAfterSAN_enPassant_fixture
#check Chess.Parsing.fenAfterSAN_castle_fixture
#check Chess.Parsing.fenAfterSAN_promotion_fixture

-- Baseline analysis correctness vs minimax spec.
#check Chess.Analysis.minimaxValue
#check Chess.Analysis.negamax_eq_minimaxValue

-- Alpha-beta window correctness scaffolding (depth-0 base + depth-1 slice).
#check Chess.Analysis.alphaBetaSound
#check Chess.Analysis.alphaBetaComplete
#check Chess.Analysis.alphaBetaSound_depth0
#check Chess.Analysis.alphaBetaComplete_depth0
#check Chess.Analysis.alphaBetaSound_depth1_worst
#check Chess.Analysis.alphaBetaComplete_depth1_worst

-- Dead-position policy is visible to analysis `terminalValue?`.
#check Chess.Analysis.drawStatus_autoDraw_of_deadPosition
#check Chess.Analysis.terminalValue?_of_deadPosition
#check Chess.Analysis.isCheckmate_false_of_terminalValue?_none
#check Chess.Analysis.deadPosition_false_of_terminalValue?_none
#check Chess.Analysis.terminalValue?_of_interpretResult_drawAuto
#check Chess.Analysis.terminalValue?_of_interpretResult_drawClaim

-- Alpha-beta list loop invariants used by the full-depth plan.
#check Chess.Analysis.alphaBetaList_ge_alpha
#check Chess.Analysis.alphaBetaList_lt_beta_cons
#check Chess.Analysis.alphaBetaListNoCutoff
#check Chess.Analysis.alphaBetaList_lt_beta_implies_eq_noCutoff

-- Early alpha-beta correctness slice (depth 1).
#check Chess.Analysis.alphaBeta_depth1_eq_minimaxValue
#check Chess.Analysis.alphaBeta_depth1_eq_negamax

-- Early alpha-beta correctness slice (depth 2).
#check Chess.Analysis.alphaBeta_depth2_eq_minimaxValue
#check Chess.Analysis.alphaBeta_depth2_eq_negamax

-- Core finiteness/extensionality primitives used by larger roundtrip proofs.
#check Chess.Square.toIndex_fromIndex
#check Chess.Square.nodup_all
#check Chess.Board.ext_get

-- Geometry helper: king-step symmetry.
#check Chess.Movement.absInt_neg
#check Chess.Movement.isKingStep_symm
#check Chess.Movement.isKingStepBool_symm
