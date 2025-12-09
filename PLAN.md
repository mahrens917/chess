# Chess Completeness Plan

The goal is a Lean chess engine whose rules are fully specified, mechanically proven, and covered by comprehensive executable tests.

## Current Status

| Category | Status |
|----------|--------|
| Sorries | 0 |
| Axioms | 21 (across Movement, Rules, Spec) |
| Theorems | Comprehensive coverage in progress |
| Tests | 14 suites passing ✓ |
| Build | Clean ✓ |

### Axiom Breakdown by Module

**Movement.lean** (2 axioms)
- `rookMove_target_at_offset` - Rook movement geometry
- `bishopMove_target_at_offset` - Bishop movement geometry

**Rules.lean** (4 axioms)
- `slidingWalk_completeness_aux` - Sliding piece trajectory
- `slidingWalk_generates_target` - Sliding piece target generation
- `slidingWalk_mem_foldr_cons` - Foldr membership for sliding walks
- `slidingWalk_in_slidingTargets` - Sliding walk to target mapping

**Spec.lean** (15 axioms)
1. **Board invariants** (2):
   - `enPassantTarget_rank_constraint` - EP targets on rank 3 or 6
   - `enPassant_target_isEmpty` - EP target squares always empty

2. **Completeness** (2):
   - `fideLegal_in_pieceTargets_axiom` - pieceTargets generates all fideLegal moves
   - `fideLegal_exact_in_pieceTargets` - Exact move membership in pieceTargets

3. **Sliding geometry** (2):
   - `rookRay_intermediates_empty` - Path between rook src/tgt is clear
   - `bishopRay_intermediates_empty` - Path between bishop src/tgt is clear

4. **Pawn logic** (7):
   - `castleMoveIfLegal_produces_fideLegal` - Castle generation correctness
   - `pawnAdvance_squareFromInts` - Square conversion for pawn advances
   - `pawnCapture_squareFromInts` - Square conversion for pawn captures
   - `pawnAdvance_singleStep_isEmpty` - Single-step target is empty
   - `pawnAdvance_twoStep_isEmpty` - Two-step intermediate/target empty
   - `enPassant_not_promo_rank` - EP captures don't reach promo rank
   - `pawnAdvance_in_forwardMoves` - Pawn advance in forward move list
   - `pawnCapture_in_captureMoves` - Pawn capture in capture move list

2. **Additional pawn axiom** (1):
   - `enPassant_target_isEmpty` (Spec.lean:1105) - Duplicate of board invariant

---

## Future Work (Priority Order)

### Phase 1: Eliminate Geometric Axioms (Movement/Rules modules)

**Status**: 6 axioms blocking complete axiom-free piece movement

1. **Movement.lean axioms** (2):
   - `rookMove_target_at_offset` - Prove rook offset calculation
   - `bishopMove_target_at_offset` - Prove bishop offset calculation

   **Action**: Extract geometric lemmas and prove via coordinate arithmetic

2. **Rules.lean axioms** (4):
   - `slidingWalk_completeness_aux` - Trajectory enumeration completeness
   - `slidingWalk_generates_target` - Sliding piece targets exhaustive
   - `slidingWalk_mem_foldr_cons` - List membership for sliding walks
   - `slidingWalk_in_slidingTargets` - Map sliding walks to board targets

   **Action**: Formalize sliding piece path enumeration as mathematical structure

### Phase 2: Eliminate Geometric Path Axioms (Spec.lean)

**Status**: 2 axioms blocking rook/bishop completeness

3. **Spec.lean axioms** (2):
   - `rookRay_intermediates_empty` (line 494) - Path clearance for rooks
   - `bishopRay_intermediates_empty` (line 506) - Path clearance for bishops

   **Action**: Prove using squaresBetween logic and coordinate arithmetic

### Phase 3: Eliminate Pawn Generation Axioms (Spec.lean)

**Status**: 5 axioms blocking pawn move completeness

4. **Spec.lean pawn axioms** (5):
   - `pawnAdvance_singleStep_isEmpty` (line 1069)
   - `pawnAdvance_twoStep_isEmpty` (line 1079)
   - `enPassant_not_promo_rank` (line 1113)
   - `pawnAdvance_in_forwardMoves` (line 1122)
   - `pawnCapture_in_captureMoves` (line 1158)

   **Action**: Prove via square arithmetic and board state analysis

### Phase 4: Eliminate Square Conversion Axioms (Spec.lean)

**Status**: 2 axioms for internal square calculations

5. **Spec.lean square axioms** (2):
   - `pawnAdvance_squareFromInts` (line 1051)
   - `pawnCapture_squareFromInts` (line 1061)

   **Action**: Extract coordinate helpers and prove square construction

### Phase 5: Eliminate Board Invariant Axioms (Spec.lean)

**Status**: 2 critical axioms blocking game state correctness

6. **Spec.lean board invariants** (2):
   - `enPassantTarget_rank_constraint` (line 113) - EP targets always on rank 3/6
   - `enPassant_target_isEmpty` (line 121) - EP targets always empty

   **Action**: Prove playMove state machine preserves invariants

   **Subtasks**:
   - Formalize playMove as state transition
   - Prove EP target set correctly on 2-square pawn push
   - Prove EP target cleared on all other moves
   - Prove invariant holds from starting position forward

### Phase 6: Complete Move Generation Logic (Spec.lean)

**Status**: 2 axioms blocking completeness of move generation

7. **Spec.lean completeness axioms** (2):
   - `fideLegal_in_pieceTargets_axiom` (line 224) - All legal moves generated
   - `fideLegal_exact_in_pieceTargets` (line 233) - Move in target list iff legal
   - `castleMoveIfLegal_produces_fideLegal` (line 1005) - Castling generation correct

   **Action**: Combine per-piece proofs with knight/king axiom-free cases

   **Dependencies**: Phases 1-5 must be complete

### Phase 7: Move Generation Soundness (New Module)

**High Priority**: Ensure generated moves are actually legal

- `allLegalMoves_sound` — All moves from allLegalMoves satisfy fideLegal
- `allLegalMoves_complete` — All fideLegal moves appear in allLegalMoves
- King safety checks for non-castling
- Pinned piece detection

### Phase 8: Game Result Correctness (New Module)

**High Priority**: Verify checkmate/stalemate/draw detection

- `checkmate_iff_inCheck_and_no_legal_moves` — Characterize checkmate
- `stalemate_iff_not_inCheck_and_no_legal_moves` — Characterize stalemate
- `draw_by_insufficient_material_correct` — K+N vs K, K+B vs K, etc.
- `draw_by_halfmove_correct` — 50-move rule (halfmove ≥ 100)
- `draw_by_repetition_correct` — Threefold/fivefold repetition

### Phase 9: Test Coverage Expansion (Executable)

- Perft validation against tablebases (current: basic smoke tests)
- SAN parsing fuzzer with round-trip validation
- FEN parsing fuzzer for edge cases (en passant, castling flags, unusual positions)
- Endgame corpus: KRK, KQK, KBBK, KBNK
- Famous games (Kasparov-Topalov 1999, Fischer-Spassky 1972, etc.)

### Phase 10: Documentation & API (Optional)

- Module-level docstrings with FIDE Law references
- Theorem proof sketches linking to Lean definitions
- API reference with board/move/game state semantics
- Update README with notation support and examples
