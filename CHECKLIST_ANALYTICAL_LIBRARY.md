# Analytical Library Completion Checklist

This checklist tracks the work needed to make this repo a “100% complete chess analytical library”:
full rule compliance, a semantic spec, end-to-end correctness proofs, computational code, tests, and
user/developer documentation.

Print settings (if you want a paper checklist):
- Two-sided (duplex), flip on long edge
- Paper size: Letter or A4
- Scale: 100% (no “fit to page”)
- Non-crossed: keep items as `[ ]/[x]` (no strikethrough styling)

Conventions:
- `[x]` done and verified in-repo
- `[ ]` not done / not yet proven / not yet implemented
- Size tags: `XS/S/M/L/XL` (rough effort estimate)

## Baseline: Build + Tests
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| `lake build` succeeds | [x] | XS |  |
| `lake test` succeeds (fast suites) | [x] | XS | Slow suites run separately via `lake exe slowtest` (see `SlowTests/Main.lean`). |
| `lake exe chessDemo` builds | [x] | XS | `Chess/Demo.lean` |
| No `sorry` in `Chess/` or `Test/` | [x] | XS | `rg -n "\\bsorry\\b" --glob '*.lean' Chess Test` |
| No deprecated `Int.ofNat_succ` usage | [x] | XS | Replaced with `Int.natCast_succ` in `Chess/PathValidationProofs.lean`. |

## Core Rules & State (Implementation)
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| Squares/board/pieces/game state modeled | [x] | S | `Chess/Core.lean` |
| Piece movement geometry encoded | [x] | S | `Chess/Movement.lean` |
| Move application updates EP/castling/promotion/clock fields | [x] | M | `Chess/Game.lean` |
| Legality filter + check detection + draw predicates | [x] | M | `Chess/Rules.lean` |
| `drawStatus`/`terminalValue?` recognize `deadPosition` | [x] | S | `Chess/Rules.lean` adds `"dead position"` to auto-draw reasons (so analysis treats it as terminal). |
| `terminalValue?` yields `0` when `deadPosition` auto-draws | [x] | S | `Chess/Analysis/TerminalValueDeadPositionProofs.lean`: `terminalValue?_of_deadPosition` (assumes `gs.result = none` and `isCheckmate = false`). |
| `terminalValue? = none` implies `deadPosition = false` | [x] | S | `Chess/Analysis/TerminalValueDeadPositionProofs.lean`: `deadPosition_false_of_terminalValue?_none` (assumes `gs.result = none`). |
| `terminalValue?` helper lemmas for draw results | [x] | S | `Chess/Analysis/TerminalValueLemmas.lean`: `terminalValue?_of_interpretResult_drawAuto`, `terminalValue?_of_interpretResult_drawClaim`. |
| `finalizeResult` records dead-position draw | [x] | S | `Chess/DeadPositionProofs.lean`: `finalizeResult_sets_draw_of_deadPosition`. |
| `finalizeResult` records insufficient-material draw | [x] | S | `Chess/DeadPositionProofs.lean`: `finalizeResult_sets_draw_of_insufficientMaterial`. |
| `playMove` records dead-position draw | [x] | S | `Chess/DeadPositionProofs.lean`: `GameState.playMove_sets_draw_of_deadPosition` (under `gs.result = none`). |
| `playMove` records insufficient-material draw | [x] | S | `Chess/DeadPositionProofs.lean`: `GameState.playMove_sets_draw_of_insufficientMaterial` (under `gs.result = none`). |
| Move generation never captures kings | [x] | S | `Chess/Rules.lean`, regression in `Test/Main.lean` |
| `playMove` snapshots history and finalizes results | [x] | M | `Chess/Rules.lean` |
| `applyLegalMoves` recursion lemmas | [x] | XS | `Chess/ApplyLegalMovesLemmas.lean` (`nil/cons` + `ok` decomposition) |

## Perft & Enumerators (Correctness)
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| `perft` implemented via `allLegalMoves` + `playMove` | [x] | S | `Chess/Rules.lean` |
| `perft_correct`: `perft gs d = (gameLines gs d).length` | [x] | M | `Chess/PerftProofs.lean` |
| Canonical perft fixture coverage documented | [x] | S | `PERFT_FIXTURES.md` (fixtures in `SlowTests/Perft.lean`). |

## Parsing / Serialization
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| FEN parse/print + validation | [x] | M | `Chess/Parsing.lean` |
| SAN generation + parsing used in tests/CLI | [x] | M | `Chess/Parsing.lean`, `Test/Main.lean`, `Chess/Demo.lean` |
| PGN parsing + replay + exports | [x] | L | `Chess/Parsing.lean`, `Chess/Export.lean` |
| Fully formal round-trip theorems for FEN/SAN/PGN | [ ] | XL | Beyond regression tests; decide “proof bar” per format. |
| FEN roundtrip (under `validateFEN`) | [x] | M | `Chess/ParsingFENGeneralRoundtripProofs.lean`: `Chess.Parsing.parseFEN_toFEN_of_validate_of_split`. Nat-field roundtrip is now formalized in `Chess/ParsingNatFieldRoundtripProofs.lean` (`Chess.Parsing.parseNatField_toString_roundtrip`). Note: `parseFEN` is whitespace-strict at the top level; `parseNatField` is also strict (no `trim`). |
| Starting position FEN is canonical (formal) | [x] | XS | `Chess/ParsingRoundtripProofs.lean`: `Chess.Parsing.toFEN_buildStartingState_eq_startFEN`. |
| Starting position SAN sanity (formal) | [x] | XS | `Chess/ParsingSANRoundtripProofs.lean`: `Chess.Parsing.moveFromSAN_start_e4`, `Chess.Parsing.applySAN_start_e4_toFEN`. |
| SAN fixtures: EP/castle/promo (formal) | [x] | S | `Chess/ParsingSANFixtureProofs.lean`: `Chess.Parsing.fenAfterSAN_enPassant_fixture`, `Chess.Parsing.fenAfterSAN_castle_fixture`, `Chess.Parsing.fenAfterSAN_promotion_fixture`. |
| FEN field roundtrips (formal) | [x] | S | `Chess/ParsingFieldRoundtripProofs.lean`: `Chess.Parsing.parseActiveColor_roundtrip`, `Chess.Parsing.parseCastlingRights_roundtrip`, `Chess.Parsing.parseEnPassant_dash_roundtrip`, `Chess.Parsing.parseEnPassant_algebraic_roundtrip`. |
| Placement roundtrip (fixture) | [x] | S | `Chess/ParsingPlacementFixtureProofs.lean`: `Chess.Parsing.parsePlacement_boardToFenPlacement_startingBoard`. |
| Placement join/split inversion (formal) | [x] | S | `Chess/ParsingPlacementRoundtripProofs.lean`: `Chess.Parsing.splitPlacementChars_joinPlacementChars` (char-level, proof-friendly). |
| Placement char encodings (formal) | [x] | XS | `Chess/ParsingCharRoundtripProofs.lean`: `Chess.Parsing.pieceFromChar_pieceToChar`, `Chess.Parsing.fenDigitValue?_digitChar_succ`. |
| Placement output has no `'/'` chars (formal) | [x] | XS | `Chess/ParsingPlacementNoSlashProofs.lean`: `Chess.Parsing.pieceToChar_ne_slash`, `Chess.Parsing.digitChar_ne_slash_of_le8`. |
| Rank placement splits back into ranks (formal) | [x] | S | `Chess/ParsingPlacementRankNoSlashProofs.lean`: `Chess.Parsing.rankToFenChars_no_slash`, `Chess.Parsing.splitPlacementChars_boardToFenPlacement`. |
| Rank parsing step lemmas (formal) | [x] | XS | `Chess/ParsingPlacementRankParsingLemmas.lean`: `Chess.Parsing.parsePlacementRankChars_pieceToChar`, `Chess.Parsing.parsePlacementRankChars_digitChar_succ`, `Chess.Parsing.parsePlacementRankChars_digitChar`. |
| Placement roundtrip (general) | [x] | L | `Chess/ParsingPlacementGeneralRoundtripProofs.lean`: `Chess.Parsing.parsePlacement_boardToFenPlacement_roundtrip`. |
| Board toList/fromList roundtrip | [x] | M | `Chess/BoardRoundtripProofs.lean`: `Chess.Board.fromList_toList`. |
| Board.fromList get semantics | [x] | M | `Chess/BoardRoundtripProofs.lean`: `Chess.Board.fromList_get_eq_none_of_forall_ne`, `Chess.Board.fromList_get_eq_some_of_mem_unique`. |

## Semantic Spec (FIDE-like) and Equivalence Proofs
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| Semantic legality predicate exists (`fideLegalSemantic`) | [x] | M | `Chess/Spec.lean` |
| Generator-exact Prop predicate exists (`encodedLegal`) | [x] | S | `Chess/RulesComplete.lean` |
| Two-sided generator equivalence: `m ∈ allLegalMoves gs ↔ encodedLegal gs m` | [x] | M | `Chess/RulesComplete.lean` |
| **Rules-complete spec:** `fideLegal := encodedLegal` | [x] | XS | `Chess/Spec.lean` |
| Two-sided rules-complete equivalence: `m ∈ allLegalMoves gs ↔ fideLegal gs m` | [x] | XS | `Chess/Spec.lean` |
| **Semantic soundness (one side):** `m ∈ Rules.allLegalMoves gs → fideLegalSemantic gs m` | [x] | XL | `Chess/SemanticFideLegalSoundness.lean`: `allLegalMoves_sound_fideLegalSemantic` (assumes `hasValidEPRank gs`); `Chess/StateInvariants.lean`: `allLegalMoves_sound_fideLegalSemantic_of_reachable` discharges the assumption for reachable states. |
| Semantic soundness (one side) assuming valid EP rank | [x] | M | `Chess/SemanticFideLegalSoundness.lean`: `allLegalMoves_sound_fideLegalSemantic` (assumes `hasValidEPRank gs`). |
| Semantic soundness (one side) for reachable states | [x] | M | `Chess/StateInvariants.lean`: `allLegalMoves_sound_fideLegalSemantic_of_reachable` (discharges `hasValidEPRank` via reachability). |
| **Semantic completeness (other side):** `fideLegalSemantic gs m → m ∈ Rules.allLegalMoves gs` | [x] | XL | `Chess/SemanticPinFilterLemmas.lean`: `fideLegalSemantic_implies_mem_allLegalMoves` (assumes `hasValidEPRank gs`); `Chess/SemanticFideLegalEquivalenceReachable.lean`: `fideLegalSemantic_iff_mem_allLegalMoves_of_reachable`. |
| Semantic castling clause binds `cfg` to move squares | [x] | L | Implemented in `Chess/Spec.lean`: `cfg.kingFrom = m.fromSq`, `cfg.kingTo = m.toSq`, and rook fields match `cfg.rookFrom/cfg.rookTo`. |
| Semantic promotion restricts `m.promotion` to `promotionTargets` | [x] | L | Implemented by strengthening the `m.promotion.isSome → ...` clause in `Chess/Spec.lean`. |
| Semantic en passant requires empty target square | [x] | M | Implemented by strengthening the pawn EP branch in `Chess/Spec.lean` (`respectsGeometry`). |
| Sliding geometry (rook/bishop/queen): targets respect `isRookMove`/`isDiagonal`/`isQueenMove` | [x] | L | `Chess/SemanticSlidingGeometryLemmas.lean` |
| Sliding `pathClear` correctness (rook/bishop/queen) | [x] | L | `Chess/SemanticSlidingPathClearLemmas.lean` |
| Sliding pieces: `pieceTargets` → `respectsGeometry` (rook/bishop/queen) | [x] | M | `Chess/SemanticSlidingRespectsGeometryLemmas.lean` |
| Pawn movement predicates (`isPawnAdvance`/`isPawnCapture`) match coordinate system | [x] | S | Fixed to use `rankDiff = -pawnDirection`; pawn checks now work and perft baselines updated to Stockfish. |
| Pawn: advances/captures/EP + promotion constraints | [x] | XL | Soundness: `Chess/SemanticFideLegalSoundness.lean`; completeness: `Chess/SemanticPawnPieceTargetsCompletenessLemmas.lean` + `Chess/SemanticPinFilterLemmas.lean`. |
| Castling safety bridge into `fideLegalSemantic` clause | [x] | L | `Chess/SemanticFideLegalSoundness.lean` uses `Chess/SemanticCastlingLemmas.lean`: `castleMoveIfLegal_implies_semantic_clause`. |
| Bool/Prop bridge for `pieceAttacksSquare`/`anyAttacksSquare` | [x] | S | `Chess/AttackSpec.lean` |
| Attack relation correctness used by `inCheck` | [x] | M | `Chess/AttackSpec.lean` + corrected pawn geometry yields check detection aligned with chess movement geometry (not pinned/“move legality”). |
| Bool/Prop bridges for king/knight geometry | [x] | S | `Chess/Movement.lean` |
| Geometry soundness for king (step+castle) + knight targets | [x] | M | `Chess/SemanticGeometryLemmas.lean` |
| PromotionMoves predicate lemmas | [x] | S | `Chess/SemanticPromotionLemmas.lean` |
| Pawn step geometry lemmas (one-step/two-step/capture) | [x] | M | `Chess/SemanticPawnLemmas.lean` |
| Any `pieceTargets` move satisfies `respectsGeometry` | [x] | M | `Chess/SemanticRespectsGeometryLemmas.lean` |
| `allLegalMoves` implies `respectsGeometry` | [x] | M | `Chess/Completeness.lean`: `allLegalMoves_sound_respectsGeometry` |
| Promotion “to last rank → promotion isSome” for reachable states | [x] | S | `Chess/StateInvariants.lean`: `mem_allLegalMoves_pawn_toPromotionRank_implies_promotion_isSome_of_reachable` |

### Breakdown: Semantic Soundness (non-crossed subgoals)

Goal: prove `m ∈ allLegalMoves gs → fideLegalSemantic gs m` without `sorry`, via compositional lemmas.

| Subgoal | Status | Size | Notes |
|---|---:|:---:|---|
| Extract `m.piece.color = gs.toMove` from membership | [x] | M | `Chess/Completeness.lean`: `allLegalMoves_sound_fideLegalCore` (extracts turn/origin/destination facts). |
| Extract `gs.board m.fromSq = some m.piece` from membership | [x] | M | `Chess/Completeness.lean`: `allLegalMoves_sound_fideLegalCore` (extracts turn/origin/destination facts). |
| Prove destination friendliness (`destinationFriendlyFreeProp`) for all generated moves | [x] | M | `Chess/Completeness.lean`: `allLegalMoves_sound_fideLegalCore` (extracts turn/origin/destination facts). |
| Prove capture flag consistency w/ EP (`captureFlagConsistentWithEP`) | [x] | L | `Chess/Completeness.lean`: `allLegalMoves_sound_captureFlagConsistentWithEP`. |
| Prove `¬inCheck (simulateMove gs m).board gs.toMove` for legal moves | [x] | XL | `Chess/Completeness.lean`: `allLegalMoves_sound_fideLegalCore` extracts `inCheck (simulateMove gs m).board gs.toMove = false` from `basicLegalAndSafe`. |
| Semantic implies generator’s `basicLegalAndSafe` filter | [x] | M | `Chess/SemanticBasicLegalLemmas.lean`: `fideLegalSemantic_implies_basicLegalAndSafe`. |
| Prove promotion constraints: “promotion iff pawn reaches last rank” | [x] | L | `Chess/SemanticFideLegalSoundness.lean` supplies both semantic clauses using `Chess/SemanticPromotionSoundnessLemmas.lean` (assumes `hasValidEPRank gs`). |
| Prove `m.isEnPassant → m.piece.pieceType = Pawn` | [x] | S | `Chess/SemanticMoveFlagLemmas.lean`: `mem_allLegalMoves_isEnPassant_implies_pawn`. |
| Prove `m.isCastle → m.piece.pieceType = King` | [x] | S | `Chess/SemanticMoveFlagLemmas.lean`: `mem_allLegalMoves_isCastle_implies_king`. |
| Prove “non-castle moves have no rook fields” | [x] | S | `Chess/SemanticNonCastleRookFieldLemmas.lean`: `mem_allLegalMoves_nonCastle_rookFields_none` (via `Chess/ParsingProofs.lean`). |
| King: standard step moves satisfy `isKingStep` | [x] | M | `Chess/SemanticGeometryLemmas.lean`: `mem_pieceTargets_king_isKingStep_of_not_castle`. |
| King: castle moves satisfy semantic castling clause | [x] | XL | `Chess/SemanticCastlingLemmas.lean`: `castleMoveIfLegal_implies_semantic_clause`. |
| Knight: membership implies `isKnightMove` | [x] | M | `Chess/SemanticGeometryLemmas.lean`: `mem_pieceTargets_knight_isKnightMove`. |
| Rook/Bishop/Queen: membership implies geometry + `pathClear` | [x] | L | Geometry: `Chess/SemanticSlidingGeometryLemmas.lean`; `pathClear`: `Chess/SemanticSlidingPathClearLemmas.lean`. |
| Pawn: non-capture advances satisfy `isPawnAdvance` + `pathClear` + start-rank constraint | [x] | XL | `Chess/SemanticPawnTargetsGeometryLemmas.lean`: `pawn_quiet_semantics_of_mem_pieceTargets` |
| Pawn: captures satisfy `isPawnCapture` + enemy-at-target | [x] | L | `Chess/SemanticPawnTargetsGeometryLemmas.lean`: `pawn_capture_semantics_of_mem_pieceTargets` |
| Pawn: en passant captures satisfy `isPawnCapture` + `gs.enPassantTarget = some m.toSq` | [x] | XL | `Chess/SemanticPawnTargetsGeometryLemmas.lean`: `pawn_capture_semantics_of_mem_pieceTargets` |

### Breakdown: Semantic Completeness (non-crossed subgoals)

Goal: prove `fideLegalSemantic gs m → m ∈ allLegalMoves gs m` constructively.

| Subgoal | Status | Size | Notes |
|---|---:|:---:|---|
| Reduce `fideLegalSemantic` into a concrete generator branch (by piece type) | [x] | XL | `Chess/SemanticPinFilterLemmas.lean`: `fideLegalSemantic_implies_mem_allLegalMoves` (assumes `hasValidEPRank gs`). |
| Show semantic geometry implies membership in `pieceTargets` | [x] | XL | Done for knight, non-castle king, sliding pieces, pawns (assuming `hasValidEPRank gs`), and castling; see `Chess/SemanticPieceTargetsCompletenessLemmas.lean`, `Chess/SemanticPawnPieceTargetsCompletenessLemmas.lean`, and `Chess/SemanticCastlingPieceTargetsCompletenessLemmas.lean`. |
| Sliding targets: walk-step membership helpers | [x] | S | `Chess/SlidingTargetsCompletenessHelpers.lean` provides accumulator monotonicity plus “current square is empty/enemy ⇒ corresponding move ∈ walk output”; these are intended for sliding-piece completeness. |
| Sliding targets: delta/offset coordinate lemmas | [x] | S | `Chess/SlidingTargetsDeltaLemmas.lean` links `rookDelta`/`rookOffset` and `bishopDelta`/`bishopOffset` to `squareFromInts`, plus `Chess.Movement.signInt_mul_natAbs`. |
| Sliding targets: rook intermediate squares exist | [x] | M | `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.squareFromInts_rookDelta_step_some` (needed to drive `slidingTargets.walk` recursion for rook-like moves). |
| Sliding targets: rook ray steps are between-squares | [x] | M | `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.rook_step_square_mem_squaresBetween` (bridge from `pathClear` to “intermediate step square is empty”). |
| Sliding targets: rookDelta is a generator delta | [x] | S | `Chess/SlidingTargetsDeltaLemmas.lean`: `Chess.Movement.rookDelta_mem_rookDeltas` (lets completeness proofs pick the correct `slidingTargets` direction). |
| Show semantic capture conditions align with generator filters | [x] | XL | Covered by `Chess/SemanticPinFilterLemmas.lean`: `fideLegalSemantic_implies_mem_allLegalMoves` plus per-piece `pieceTargets` completeness and the generator’s `basicLegalAndSafe` filter. |
| Show semantic safety (`¬inCheck`) implies membership in `allLegalMoves` filter | [x] | XL | `Chess/SemanticBasicLegalLemmas.lean`: `fideLegalSemantic_implies_basicLegalAndSafe` provides `basicLegalAndSafe gs m = true`. |
| Semantic completeness (all pieces) | [x] | M | `Chess/SemanticPinFilterLemmas.lean`: `fideLegalSemantic_implies_mem_allLegalMoves` (assumes `hasValidEPRank gs`). |
| Two-sided equivalence (`semantic ↔ generator ↔ encodedLegal`) | [x] | S | `Chess/SemanticFideLegalEquivalence.lean`: `fideLegalSemantic_iff_mem_allLegalMoves`, `fideLegalSemantic_iff_fideLegal` (assumes `hasValidEPRank gs`). |
| Two-sided equivalence (reachable states) | [x] | XS | `Chess/SemanticFideLegalEquivalenceReachable.lean`: `fideLegalSemantic_iff_mem_allLegalMoves_of_reachable`, `fideLegalSemantic_iff_fideLegal_of_reachable` (discharges `hasValidEPRank gs`). |
| Promotion completeness: semantic promotion implies membership in `promotionMoves` output | [x] | L | `Chess/SemanticPromotionLemmas.lean`: `mem_promotionMoves_of_mem_promotionTargets`. |

### Breakdown: Attack / Check Correctness (non-crossed subgoals)

Goal: make `inCheck` trustworthy for semantic proofs.

| Subgoal | Status | Size | Notes |
|---|---:|:---:|---|
| Define Prop-level “attacks” relation (per piece) | [x] | M | `Chess/AttackSpec.lean`: `attacksSpec`. |
| King attacks: Bool/Prop equivalence | [x] | S | `Chess/AttackSpec.lean`: `pieceAttacksSquare_eq_true_iff_attacksSpec` (king branch). |
| Knight attacks: Bool/Prop equivalence | [x] | S | `Chess/AttackSpec.lean`: `pieceAttacksSquare_eq_true_iff_attacksSpec` (knight branch). |
| Sliding attacks: Bool uses `decide isRookMove/isDiagonal` + `pathClear` | [x] | L | `Chess/AttackSpec.lean`: `pieceAttacksSquare_eq_true_iff_attacksSpec` (queen/rook/bishop branches). |
| Pawn attacks: Bool vs `isPawnCapture` semantics | [x] | L | `Chess/AttackSpec.lean`: `pieceAttacksSquare_eq_true_iff_attacksSpec` (pawn branch). |
| `anyAttacksSquare` correctness (exists attacker iff Bool true) | [x] | XL | `Chess/AttackSpec.lean`: `anyAttacksSquare_eq_true_iff_exists_attacker`. |
| `inCheck` correctness (kingSquare + anyAttacksSquare) | [x] | L | `Chess/AttackSpec.lean`: `inCheck_eq_true_iff_exists_attacker`. |
| King-step symmetry lemma | [x] | XS | `Chess/Movement.lean`: `Chess.Movement.isKingStep_symm` (used for king-vs-king semantic dead-position work). |

## End Conditions & Draw Rules (Correctness)
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| Checkmate/stalemate equivalences to spec-level definitions | [x] | S | `Chess/EndConditionsSpec.lean` |
| Repetition correctness vs stored `history` snapshots | [x] | M | `Chess/HistorySpec.lean` shows `playMove` appends `positionSnapshot` and repetition counts snapshots. |
| 50/75-move draw correctness vs explicit spec | [x] | S | `Chess/DrawSpec.lean`, `Test/DrawProofs.lean` |
| `insufficientMaterial` / `deadPosition`: rules-complete wrappers (`= true`) | [x] | XS | `Chess/MaterialSpec.lean` |
| `isDeadPosition`: formal definition uses legal move sequences | [x] | XS | `Chess/Rules.lean` quantifies via `applyLegalMoves` (not arbitrary `playMove`). |
| `insufficientMaterial` / `deadPosition`: semantic/FIDE correctness | [ ] | XL | Requires a precise semantic rule statement for “dead position”. |
| K vs K: `isDeadPosition` (semantic instance) | [x] | S | `Chess/KkDeadPositionProofs.lean`: `Chess.Rules.isDeadPosition_kkGameState` (assumes non-adjacent kings). |
| K+N vs K: `isDeadPosition` (semantic instance) | [ ] | L | Prove from a “kings + one knight” invariant and closure under `applyLegalMoves`. |
| K+B vs K: `isDeadPosition` (semantic instance) | [ ] | L | Prove from a “kings + one bishop” invariant and closure under `applyLegalMoves`. |
| K+NN vs K: `isDeadPosition` (semantic instance) | [ ] | XL | Checkmate should be impossible with only two knights; proof likely needs a “no-mate” lemma for every checked-king situation. |
| K+BB same-color vs K: `isDeadPosition` (semantic instance) | [ ] | XL | Checkmate should be impossible with bishops on one color complex; proof likely needs an invariant about unattacked escape squares. |
| `deadPosition` Bool heuristic implies `isDeadPosition` Prop | [ ] | XL | Optional: prove for the subset of heuristic cases that are truly dead (or restrict to reachable/legal positions). |
| Endgame dead-position plan documented | [x] | XS | `ENDGAME_DEAD_POSITION_PLAN.md` |
| Kings+minor move-shape lemmas (no castle/EP/promo, src/piece cases) | [x] | S | `Chess/KMinorMoveLemmas.lean` |
| Kings+minor `movePiece` board update lemma | [x] | S | `Chess/KMinorUpdateLemmas.lean` |
| Kings+minor capture transition lemmas | [x] | M | `Chess/KMinorTransitionLemmas.lean` |
| Kings+minor source-square lemmas (piece → fromSq) | [x] | S | `Chess/KMinorSourceLemmas.lean` |
| Kings+minor capture classification lemmas | [x] | S | `Chess/KMinorCaptureLemmas.lean` |
| Kings+minor non-capture preservation lemma | [x] | M | `Chess/KMinorPreservationLemmas.lean` |
| K+minor closure under `applyLegalMoves` (kings+minor stays or collapses to K vs K) | [x] | M | `Chess/KMinorDeadPositionInvariants.lean`: `KMinorOrKkInv.applyLegalMoves_preserved`. |
| K+N/K+B closure under `applyLegalMove` (or collapse to K vs K) | [x] | M | `Chess/KMinorSpecificEndgameInvariants.lean`: `KknInv.applyLegalMove_preserved_or_kkInv`, `KkbInv.applyLegalMove_preserved_or_kkInv`. |
| K+minor: “checked lone king has a legal escape move” lemma | [ ] | M | Needed to prove K+N/K+B semantic dead positions; see `ENDGAME_DEAD_POSITION_PLAN.md`. |

## Semantic (FIDE-Like) Legality & Reachability
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| Soundness: `allLegalMoves → fideLegalSemantic` | [x] | M | `Chess/SemanticFideLegalSoundness.lean` (assumes `hasValidEPRank`). |
| Completeness: `fideLegalSemantic → allLegalMoves` | [ ] | XL | Target: full completeness theorem or reachable-state completeness. |
| Equivalence (unrestricted): `fideLegalSemantic ↔ fideLegal` | [ ] | XL | Likely requires additional invariants (king existence, EP rank, etc.). |
| Equivalence (reachable): `reachableFromStandard → (fideLegalSemantic ↔ fideLegal)` | [ ] | XL | `Chess/SemanticFideLegalEquivalenceReachable.lean` is the natural home. |
| Define/maintain `reachableFromStandard` invariants | [ ] | L | Capture king existence, non-adjacent kings, EP rank, etc., and show `playMove` preserves them. |

## Engine / Analysis Layer (If In Scope)
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| Decide analysis scope (depth-limited vs engine-grade) | [x] | S | Current choice: minimal deterministic depth-limited search (see `ANALYSIS_ENGINE_PLAN.md`). |
| Define evaluation + minimax value spec | [x] | L | `Chess/Analysis/Spec.lean`: `staticEval`, `terminalValue?`, `mateScore`; `Chess/Analysis/MinimaxSpec.lean`: `minimaxValue`. |
| Implement alpha-beta (negamax form) | [x] | M | `Chess/Analysis/AlphaBeta.lean`: `alphaBetaValue`, `alphaBeta` (tests compare values to `negamax` for small fixtures). |
| Prove alpha-beta equivalent to `minimaxValue` | [ ] | XL | Started: depth-1 (`Chess/Analysis/AlphaBetaDepth1Proofs.lean`) and depth-2 (`Chess/Analysis/AlphaBetaDepth2Proofs.lean`) correctness; full depth equivalence still needed. |
| Alpha-beta window-correctness scaffolding module | [x] | S | `Chess/Analysis/AlphaBetaWindow.lean` packages depth-0 + depth-1 “window correctness” statements used by the full-depth roadmap. |
| Alpha-beta list-scan invariants (monotonic α) | [x] | S | `Chess/Analysis/AlphaBetaListLemmas.lean`: `alphaBetaList_ge_alpha`. |
| Alpha-beta list-scan no-cutoff lemma (`< β`) | [x] | S | `Chess/Analysis/AlphaBetaListLemmas.lean`: `alphaBetaList_lt_beta_cons`. |
| Alpha-beta list-scan no-prune equals scan | [x] | M | `Chess/Analysis/AlphaBetaListLemmas.lean`: `alphaBetaListNoCutoff`, `alphaBetaList_lt_beta_implies_eq_noCutoff`. |
| Alpha-beta full correctness plan documented | [x] | S | `ALPHABETA_FULL_CORRECTNESS_PLAN.md` (windowed correctness + induction roadmap). |
| Implement baseline search (slow but obvious) | [x] | M | `Chess/Analysis/Baseline.lean`: `negamax`, `negamaxPV` (deterministic first-max tie-break). |
| Prove baseline search equals minimax value spec | [x] | L | `Chess/Analysis/Equivalence.lean`: `negamax_eq_minimaxValue`, `negamaxPV_value_eq_minimaxValue`. |
| Repetition-aware search consistent with `finalizeResult` | [ ] | XL | Must align with draw rules + history model. |
| PV extraction + legality/correctness lemmas | [x] | L | `Chess/Analysis/Proofs.lean`: `pvLegal_negamaxPV`, `pvLength_negamaxPV`, `negamaxPV_value_ge_moveScore`, `negamaxPV_value_eq_headScore`, `negamaxPV_headScore_ge_moveScore`. |
| Optional performance layer: bitboards + refinement proofs | [ ] | XL | Pure optimization layer with proof of equivalence to baseline. |

## Documentation
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| High-level README with build/test/demo usage | [x] | S | `README.md` |
| Stable library API guide | [x] | M | `API_GUIDE.md` |
| Theorem index (where the key theorems live) | [x] | S | `THEOREM_INDEX.md` |
| “Assumptions & scope” separated (FIDE-complete vs heuristics vs research) | [x] | S | `ASSUMPTIONS_AND_SCOPE.md` |
| Parser proof bar documented (FEN/SAN/PGN) | [x] | S | `PARSER_PROOF_BAR.md` |
| Analysis/engine plan documented | [x] | S | `ANALYSIS_ENGINE_PLAN.md` |

## Acceptance Gate (“100% complete”)
| Item | Status | Size | Notes |
|---|---:|:---:|---|
| Choose the formal bar | [x] | XS | Current bar defined in `ACCEPTANCE_GATE.md`. |
| Rules-complete gate (two-sided, non-crossed) | [x] | M | Acceptance now explicitly includes `playMove` invariants and “no king capture” enforcement (`ACCEPTANCE_GATE.md`, `Test/AcceptanceGate.lean`). |
| Analysis-complete gate (two-sided, non-crossed) | [ ] | XL | Baseline `negamax` now matches `minimaxValue`, but any optimization layer still needs equivalence proofs. |
| Engine-grade gate (two-sided, non-crossed) | [ ] | XL | Requires refinement proofs for representation/performance layers. |
| README points to exact proofs/tests for chosen bar | [x] | S | See `ACCEPTANCE_GATE.md` and the corresponding compiled `Test/AcceptanceGate.lean`. |
