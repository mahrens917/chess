# Theorem Index

This is a curated map of “key theorems” for navigation. It is not exhaustive.

## Rules-Complete (Move Generator Spec)

- `Chess/RulesComplete.lean`: `mem_allLegalMoves_iff_encodedLegal`
- `Chess/Spec.lean`: `allLegalMoves_iff_fideLegal` (where `fideLegal := encodedLegal`)

## Perft

- `Chess/PerftProofs.lean`: `perft_correct` (`perft gs d = (gameLines gs d).length`)

## Core Encoding

- `Chess/Core.lean`: `Chess.Square.toIndex_fromIndex` (indexing roundtrip)
- `Chess/Core.lean`: `Chess.Square.nodup_all` (finite square enumeration is nodup)
- `Chess/Core.lean`: `Chess.Board.ext_get` (board extensionality by `get`)
- `Chess/BoardRoundtripProofs.lean`: `Chess.Board.fromList_toList` (reconstruct board from `toList`)
- `Chess/BoardRoundtripProofs.lean`: `Chess.Board.fromList_get_eq_none_of_forall_ne`
- `Chess/BoardRoundtripProofs.lean`: `Chess.Board.fromList_get_eq_some_of_mem_unique`

## Draw Rules

- `Chess/Rules.lean`: draw specs/iff lemmas for 50/75-move and repetition
- `Test/DrawProofs.lean`: lightweight type-checking + example usage of those specs

## Attacks / Check

- `Chess/AttackSpec.lean`: `pieceAttacksSquare_eq_true_iff_attacksSpec`
- `Chess/AttackSpec.lean`: `anyAttacksSquare_eq_true_iff_exists_attacker`
- `Chess/AttackSpec.lean`: `inCheck_eq_true_iff_exists_attacker`

## Sliding Geometry

- `Chess/SemanticSlidingGeometryLemmas.lean`: `mem_pieceTargets_rook_isRookMove`, `mem_pieceTargets_bishop_isDiagonal`, `mem_pieceTargets_queen_isQueenMove`
- `Chess/SemanticSlidingRespectsGeometryLemmas.lean`: `respectsGeometry_of_pieceTargets_rook`, `respectsGeometry_of_pieceTargets_bishop`, `respectsGeometry_of_pieceTargets_queen`

## Sliding Path Clearance

- `Chess/SemanticSlidingPathClearLemmas.lean`: `mem_pieceTargets_rook_pathClear`, `mem_pieceTargets_bishop_pathClear`, `mem_pieceTargets_queen_pathClear`

## Pawn Geometry

- `Chess/SemanticPawnLemmas.lean`: `isPawnAdvance_of_oneStep`, `isPawnAdvance_of_twoStep`, `isPawnCapture_of_step`
- `Chess/SemanticPawnTargetsGeometryLemmas.lean`: `respectsGeometry_of_pieceTargets_pawn`

## Geometry Dispatcher

- `Chess/SemanticRespectsGeometryLemmas.lean`: `respectsGeometry_of_pieceTargets`

## Move Flags

- `Chess/SemanticMoveFlagLemmas.lean`: `mem_allLegalMoves_isEnPassant_implies_pawn`
- `Chess/SemanticMoveFlagLemmas.lean`: `mem_allLegalMoves_isCastle_implies_king`

## Capture Flags

- `Chess/Completeness.lean`: `allLegalMoves_sound_captureFlagConsistentWithEP`
- `Chess/SemanticCaptureFlagLemmas.lean`: `captureFlagConsistent_of_destinationFriendlyFree_and_captureFlagConsistentWithEP`

## Basic Legality

- `Chess/SemanticBasicLegalLemmas.lean`: `fideLegalSemantic_implies_basicLegalAndSafe`

## Piece Target Completeness

- `Chess/SemanticPieceTargetsCompletenessLemmas.lean`: `fideLegalSemantic_implies_mem_pieceTargets_knight`
- `Chess/SemanticPieceTargetsCompletenessLemmas.lean`: `fideLegalSemantic_implies_mem_pieceTargets_king_not_castle`
- `Chess/SemanticPieceTargetsCompletenessLemmas.lean`: `fideLegalSemantic_implies_mem_pieceTargets_rook`
- `Chess/SemanticPieceTargetsCompletenessLemmas.lean`: `fideLegalSemantic_implies_mem_pieceTargets_bishop`
- `Chess/SemanticPieceTargetsCompletenessLemmas.lean`: `fideLegalSemantic_implies_mem_pieceTargets_queen`
- `Chess/SemanticPawnPieceTargetsCompletenessLemmas.lean`: `fideLegalSemantic_implies_mem_pieceTargets_pawn` (assumes `hasValidEPRank gs`)
- `Chess/SemanticCastlingPieceTargetsCompletenessLemmas.lean`: `fideLegalSemantic_implies_mem_pieceTargets_king_castle`
- `Chess/SemanticPromotionSoundnessLemmas.lean`: `mem_pawn_pieceTargets_promotion_eq_some_implies_mem_promotionTargets`

## Sliding Walk Helpers

- `Chess/SlidingTargetsCompletenessHelpers.lean`: `slidingTargets_walk_acc_subset`
- `Chess/SlidingTargetsCompletenessHelpers.lean`: `slidingTargets_walk_mem_of_empty_square`
- `Chess/SlidingTargetsCompletenessHelpers.lean`: `slidingTargets_walk_mem_of_enemy_square`

## Sliding Delta Helpers

- `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.signInt_mul_natAbs`
- `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.squareFromInts_rookDelta_rookOffset`
- `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.squareFromInts_bishopDelta_bishopOffset`
- `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.squareFromInts_rookDelta_step_some`
- `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.rookDelta_mem_rookDeltas`
- `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.rook_step_square_mem_squaresBetween`

## Basic Geometry Helpers

- `Chess/Movement.lean`: `Chess.Movement.absInt_neg`, `Chess.Movement.isKingStep_symm`, `Chess.Movement.isKingStepBool_symm`
## Non-Castle Fields

- `Chess/SemanticNonCastleRookFieldLemmas.lean`: `mem_allLegalMoves_nonCastle_rookFields_none`

## Promotion Soundness

- `Chess/SemanticPromotionSoundnessLemmas.lean`: `mem_allLegalMoves_promotion_isSome_implies_pawn_and_rank`
- `Chess/SemanticPromotionSoundnessLemmas.lean`: `mem_allLegalMoves_pawn_toPromotionRank_implies_promotion_isSome` (assumes `hasValidEPRank gs`)
- `Chess/StateInvariants.lean`: `mem_allLegalMoves_pawn_toPromotionRank_implies_promotion_isSome_of_reachable` (discharges `hasValidEPRank` for reachable states)
- `Chess/SemanticPromotionLemmas.lean`: `mem_promotionMoves_of_mem_promotionTargets`

## Semantic Soundness

- `Chess/SemanticFideLegalSoundness.lean`: `allLegalMoves_sound_fideLegalSemantic` (assumes `hasValidEPRank gs`)
- `Chess/StateInvariants.lean`: `allLegalMoves_sound_fideLegalSemantic_of_reachable` (discharges `hasValidEPRank` for reachable states)

## Semantic Completeness

- `Chess/SemanticFideLegalEquivalence.lean`: `fideLegalSemantic_iff_mem_allLegalMoves` (assumes `hasValidEPRank gs`)
- `Chess/SemanticFideLegalEquivalence.lean`: `fideLegalSemantic_iff_fideLegal` (assumes `hasValidEPRank gs`)
- `Chess/SemanticFideLegalEquivalenceReachable.lean`: `fideLegalSemantic_iff_mem_allLegalMoves_of_reachable`
- `Chess/SemanticFideLegalEquivalenceReachable.lean`: `fideLegalSemantic_iff_fideLegal_of_reachable`
- `Chess/SemanticPinFilterLemmas.lean`: `fideLegalSemantic_implies_mem_allLegalMoves` (assumes `hasValidEPRank gs`)
- `Chess/SemanticPinFilterLemmas.lean`: `fideLegalSemantic_implies_mem_allLegalMoves_of_not_knight` (assumes `hasValidEPRank gs`)

## State Invariants / Reachability

- `Chess/StateInvariants.lean`: `reachableFromStandard`
- `Chess/StateInvariants.lean`: `reachableFromStandard_hasValidEPRank`
- `Chess/StateInvariants.lean`: `hasValidEPRank_playMove_of_mem_allLegalMoves`

## King Safety (No King Capture)

- `Chess/Rules.lean`: `mem_allLegalMoves_implies_destinationFriendlyFree`
- `Chess/Rules.lean`: `mem_allLegalMoves_implies_not_king_destination`

## Path Helpers

- `Chess/PathValidationProofs.lean`: `Rules.pathClear_eq_true_iff` (bridge lemma for reasoning about `pathClear`)

## End Conditions

- `Chess/EndConditionsSpec.lean`: Prop specs + iff theorems for `isCheckmate` and `isStalemate`

## Draw Specs

- `Chess/DrawSpec.lean`: Bool/Prop bridges for 50/75-move and repetition helpers
- `Chess/HistorySpec.lean`: `GameState.playMove_history`, `threefoldRepetition_eq_count`, `fivefoldRepetition_eq_count`
- `Chess/MaterialSpec.lean`: `insufficientMaterialExact`, `deadPositionHeuristic`
- `Chess/DeadPositionProofs.lean`: `drawStatus_autoDraw_of_deadPosition`, `interpretResult_of_deadPosition`, `finalizeResult_sets_draw_of_deadPosition`
- `Chess/DeadPositionProofs.lean`: `finalizeResult_sets_draw_of_insufficientMaterial`, `GameState.playMove_sets_draw_of_insufficientMaterial`
- `Chess/DeadPositionProofs.lean`: `GameState.playMove_sets_draw_of_deadPosition`
- `Chess/ApplyLegalMovesLemmas.lean`: `applyLegalMoves_nil`, `applyLegalMoves_cons`, `applyLegalMoves_eq_ok_cons_iff`
- `Chess/KkDeadPositionProofs.lean`: `isDeadPosition_kkGameState` (K vs K with non-adjacent kings is dead-position by the legal-sequence definition)
- `Chess/KkDeadPositionProofs.lean`: `KkInv.isDeadPosition`, `isDeadPosition_of_KingsOnly` (reusable K-vs-K dead-position lemmas)
- `Chess/KMinorBoard.lean`: `KingsPlusMinor.castleMoveIfLegal_none` (castling is impossible with only kings + one minor)
- `Chess/KMinorBoard.lean`: `KingsPlusMinor.inCheck_white_implies_minor_attacker`, `KingsPlusMinor.inCheck_black_implies_minor_attacker` (on kings+minor boards, any check comes from the minor if kings are non-adjacent)
- `Chess/KMinorBoard.lean`: `KingsPlusMinor.inCheck_white_of_isKingStep`, `KingsPlusMinor.inCheck_black_of_isKingStep` (adjacent kings imply check via the attacker-exists characterization)
- `Chess/KMinorMoveLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_isCastle_false` (no castling moves are generated on kings+minor boards)
- `Chess/KMinorMoveLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_fromSq` (any legal move originates from one of the three occupied squares)
- `Chess/KMinorMoveLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_piece_cases` (any legal move uses one of the three pieces)
- `Chess/KMinorMoveLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_isEnPassant_false` (no EP moves are generated on kings+minor boards)
- `Chess/KMinorMoveLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_promotion_none` (no promotion moves are generated on kings+minor boards)
- `Chess/KMinorUpdateLemmas.lean`: `KingsPlusMinor.movePiece_board_eq_update_update` (under those “no special move” facts, `movePiece` is just `update from none` then `update to piece`)
- `Chess/KMinorTransitionLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_destination_empty_or_minorSquare` (a legal move’s destination is either empty or the minor’s square)
- `Chess/KMinorTransitionLemmas.lean`: `KingsPlusMinor.whiteKing_captureMinor_yields_kingsOnly`, `KingsPlusMinor.blackKing_captureMinor_yields_kingsOnly` (a king capturing the minor collapses to `KingsOnly`)
- `Chess/KMinorSourceLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_fromSq_eq_wk_of_piece_whiteKing`, `KingsPlusMinor.mem_allLegalMoves_fromSq_eq_bk_of_piece_blackKing`, `KingsPlusMinor.mem_allLegalMoves_fromSq_eq_msq_of_piece_minor` (ties `m.piece` to the unique source square on kings+minor boards)
- `Chess/KMinorCaptureLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_isCapture_implies_toSq_minorSquare`, `KingsPlusMinor.mem_allLegalMoves_isCapture_implies_piece_is_opponentKing`, `KingsPlusMinor.mem_allLegalMoves_isCapture_implies_fromSq_opponentKingSquare` (classifies capture moves in kings+minor as “opponent king captures the minor”)
- `Chess/KMinorPreservationLemmas.lean`: `KingsPlusMinor.mem_allLegalMoves_isCapture_false_implies_toSq_empty`, `KingsPlusMinor.mem_allLegalMoves_isCapture_false_preserves` (non-capture moves preserve the kings+minor invariant, with updated king/minor square)
- `Chess/KMinorDeadPositionInvariants.lean`: `KMinorInv.applyLegalMove_preserved_or_kkInv`, `KMinorOrKkInv.applyLegalMoves_preserved` (closure under legal move sequences: kings+minor stays kings+minor or collapses to kings-only)
- `Chess/KMinorSpecificEndgameInvariants.lean`: `KknInv.applyLegalMove_preserved_or_kkInv`, `KkbInv.applyLegalMove_preserved_or_kkInv` (closure for K+N and K+B, collapsing to K vs K on capture)

## Analysis (Work In Progress)

- `Chess/Analysis/Spec.lean`: `staticEval`, `terminalValue?`, `mateScore`
- `Chess/Analysis/MinimaxSpec.lean`: `minimaxValue`
- `Chess/Analysis/Baseline.lean`: `negamax`, `negamaxPV`
- `Chess/Analysis/AlphaBeta.lean`: `alphaBetaValue`, `alphaBeta`
- `Chess/Analysis/Bounds.lean`: bounds for `staticEval` / `minimaxValue 0`
- `Chess/Analysis/MinimaxBounds.lean`: `minimaxValue_bounds`
- `Chess/Analysis/AlphaBetaWindow.lean`: `alphaBetaSound`, `alphaBetaComplete` (depth-0 base + depth-1 window slice)
- `Chess/Analysis/TerminalValueDeadPositionProofs.lean`: `drawStatus_autoDraw_of_deadPosition`, `terminalValue?_of_deadPosition`
- `Chess/Analysis/TerminalValueDeadPositionProofs.lean`: `isCheckmate_false_of_terminalValue?_none`, `deadPosition_false_of_terminalValue?_none`
- `Chess/Analysis/TerminalValueLemmas.lean`: `terminalValue?_of_interpretResult_drawAuto`, `terminalValue?_of_interpretResult_drawClaim`
- `Chess/Analysis/AlphaBetaListLemmas.lean`: `alphaBetaList_ge_alpha`, `alphaBetaList_lt_beta_cons`, `alphaBetaList_lt_beta_implies_eq_noCutoff`
- `Chess/Analysis/AlphaBetaDepth1Proofs.lean`: `alphaBeta_depth1_eq_minimaxValue`, `alphaBeta_depth1_eq_negamax`
- `Chess/Analysis/AlphaBetaDepth2Proofs.lean`: `alphaBeta_depth2_eq_minimaxValue`, `alphaBeta_depth2_eq_negamax`
- `Chess/Analysis/Equivalence.lean`: `negamaxPV_value_eq_minimaxValue`, `negamax_eq_minimaxValue`
- `Chess/Analysis/Proofs.lean`: `pvLegal_negamaxPV`, `pvLength_negamaxPV`, `negamaxPV_value_ge_moveScore`, `negamaxPV_value_eq_headScore`, `negamaxPV_headScore_ge_moveScore`

## Parsing / Notation

- `Chess/Parsing_SAN_Proofs.lean`: SAN-focused proof layer
- `Chess/ParsingProofs.lean`: broader parsing-related proof and validation surface
- `Chess/ParsingRoundtripProofs.lean`: `Chess.Parsing.toFEN_buildStartingState_eq_startFEN`
- `Chess/ParsingFieldRoundtripProofs.lean`: `Chess.Parsing.parseActiveColor_roundtrip`, `Chess.Parsing.parseCastlingRights_roundtrip`, `Chess.Parsing.parseEnPassant_dash_roundtrip`, `Chess.Parsing.parseEnPassant_algebraic_roundtrip`
- `Chess/ParsingSANRoundtripProofs.lean`: `Chess.Parsing.moveFromSAN_start_e4`, `Chess.Parsing.applySAN_start_e4_toFEN`
- `Chess/ParsingSANFixtureProofs.lean`: `Chess.Parsing.fenAfterSAN_enPassant_fixture`, `Chess.Parsing.fenAfterSAN_castle_fixture`, `Chess.Parsing.fenAfterSAN_promotion_fixture`
- `Chess/ParsingPlacementFixtureProofs.lean`: `Chess.Parsing.parsePlacement_boardToFenPlacement_startingBoard`
- `Chess/ParsingPlacementRoundtripProofs.lean`: `Chess.Parsing.splitPlacementChars_joinPlacementChars`
- `Chess/ParsingCharRoundtripProofs.lean`: `Chess.Parsing.pieceFromChar_pieceToChar`, `Chess.Parsing.fenDigitValue?_digitChar_succ`
- `Chess/ParsingPlacementNoSlashProofs.lean`: `Chess.Parsing.pieceToChar_ne_slash`, `Chess.Parsing.digitChar_ne_slash_of_le8`
- `Chess/ParsingPlacementRankNoSlashProofs.lean`: `Chess.Parsing.rankToFenChars_no_slash`, `Chess.Parsing.splitPlacementChars_boardToFenPlacement`
- `Chess/ParsingPlacementRankParsingLemmas.lean`: `Chess.Parsing.parsePlacementRankChars_pieceToChar`, `Chess.Parsing.parsePlacementRankChars_digitChar_succ`, `Chess.Parsing.parsePlacementRankChars_digitChar`
- `PARSER_PROOF_BAR.md`: chosen proof bar for formats (what “complete” means)

## Proof Umbrella

- `Chess/Proofs.lean`: imports all proof layers to keep the proof graph “on build”
