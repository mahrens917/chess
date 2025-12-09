# Phase 3 Axiom Elimination - Strategic Plan

## Current Status
**Axioms Remaining**: 10 (down from 21 = 53% already eliminated)

## Remaining Axioms by Category & Tractability

### Category 1: Game State Invariants (MEDIUM DIFFICULTY)
**Remaining**: 2 axioms (duplicates)
- Line 126: `enPassant_target_isEmpty (gs : GameState) (target : Square)`
- Line 1193: `enPassant_target_isEmpty (gs : GameState) (sq : Square)` (DUPLICATE)

**Status**: Duplicates - should consolidate
**Challenge**: Requires understanding game state machine invariants
**Approach**:
- Remove duplicate at line 1193
- Prove that enPassant targets are always empty as a consequence of:
  - movePiece only sets EP on 2-step pawn moves
  - pathClear validates intermediate squares are empty
  - Requires connecting board state before/after move

**Estimated Effort**: 4-5 hours (once duplicate removed)
**Value**: 1 axiom (consolidates 2 duplicates)

### Category 2: Foundational Coordinate Axiom (INTENTIONAL)
- `squareFromInts_roundTrip` (1 axiom)

**Status**: Accepted as foundational (documented)
**Rationale**: Type invariant similar to Lean's Int axioms

---

### Category 3: Path Validation (HIGH COMPLEXITY)
**Remaining**: 2 axioms
- `rookRay_intermediates_empty` (line 513)
- `bishopRay_intermediates_empty` (line 525)

**Deferred From**: Phase 2B
**Challenge**: Requires proving offset k maps to squaresBetween membership via filterMap
**Approach**:
- Create generic squaresBetween membership lemmas
- Prove squares enumerated correctly by filterMap
- Connect to pathClear's .all property

**Estimated Effort**: 3-4 hours
**Value**: 2 axioms
**Priority**: High (enables move completeness proofs later)

---

### Category 4: Move List Membership (COMPLEX PATTERN MATCHING)
**Remaining**: 2 axioms
- `pawnAdvance_in_forwardMoves` (line 1237)
- `pawnCapture_in_captureMoves` (line 1273)

**Deferred From**: Phase 2C
**Challenge**: Nested match/if with conditional list construction + foldr semantics
**Approach**:
- Develop reusable foldr membership lemmas
- Handle conditional list construction in foldr
- Case analysis on isEmpty conditions

**Estimated Effort**: 4-6 hours each (8-12 total)
**Value**: 2 axioms
**Priority**: Medium (enables pawn move completeness)
**Note**: Proof patterns could be reused for other piece types in Phase 4+

---

### Category 5: Move Completeness (VERY HIGH COMPLEXITY)
**Remaining**: 2 axioms
- `fideLegal_in_pieceTargets_axiom` (line 229)
- `fideLegal_exact_in_pieceTargets` (line 238)

**Challenge**: Meta-theorems requiring proofs for all piece types
**Dependencies**: Requires path validation and move list membership proofs
**Approach**:
- Decompose by piece type (6 cases: Pawn, Knight, Bishop, Rook, Queen, King)
- Use existing partial proofs (`fideLegal_pawn_in_pieceTargets`, `fideLegal_king_castle_in_pieceTargets`)
- Prove remaining piece cases

**Estimated Effort**: 12-16 hours
**Value**: 2 axioms (but highest impact for completeness)
**Priority**: Low initially (requires dependencies)
**Phases**: Could be Phase 4+ work

---

### Category 6: Castling Logic (MEDIUM DIFFICULTY)
**Remaining**: 1 axiom
- `castleMoveIfLegal_produces_fideLegal` (line 1024)

**Challenge**: Castling rule complexity + king/rook interaction
**Status**: Has corresponding theorem `fideLegal_king_castle_in_pieceTargets` (line 1036)
**Approach**:
- Understand castling move construction
- Prove that castleMoveIfLegal results satisfy fideLegal conditions
- Handle both kingside and queenside cases

**Estimated Effort**: 3-4 hours
**Value**: 1 axiom
**Priority**: Medium

---

## Recommended Phase 3 Execution Plan

### Stage 3A: Code Cleanup (1 hour)
1. ✅ Consolidate duplicate `enPassant_target_isEmpty` axioms
2. Review axiom grouping and organization

### Stage 3B: Quick Wins (2-3 axioms, 4-5 hours)
Priority: High Value/Low Effort

Options:
1. **Castling Logic** (3-4 hours, 1 axiom)
   - Clean relative to path validation
   - Focused scope (castling-specific)
   - Start: Understand castleMoveIfLegal → understand expected move structure

2. **Path Validation Analysis** (prepare foundation)
   - Create squaresBetween membership lemmas
   - Establish patterns for geometric proofs

### Stage 3C: Medium Complexity (4-6 hours, 2 axioms)
Priority: Value + Sets up downstream work

1. **Path Validation Proofs** (3-4 hours, 2 axioms)
   - Builds on Stage 3B groundwork
   - Enables move completeness proofs

2. **Move List Membership** (4-6 hours, 2 axioms - optional)
   - If time permits
   - Complex but creates reusable patterns

### Stage 3D: High Effort, High Impact (12-16 hours, 2 axioms - Phase 4+)
**Move Completeness Theorems**
- Defer unless significant time available
- Required for complete axiom elimination
- Depends on Stage 3B/3C work

---

## Critical Insights for Phase 3

### 1. Duplicate Consolidation Priority
Two identical `enPassant_target_isEmpty` axioms exist. Consolidate immediately to:
- Reduce axiom count from 10 to 9
- Simplify proofs (single target axiom)
- Clean up code organization

### 2. Dependency Chain
```
squareFromInts_roundTrip (✅ foundational)
    ├─→ pawnAdvance/Capture_squareFromInts (✅ proven)
    └─→ pawn move list membership (deferred, high complexity)

pathClear definition
    ├─→ Path validation proofs (deferred, medium complexity)
    └─→ Move completeness (deferred, very high complexity)

enPassant_target_isEmpty
    ├─→ Requires game state machine understanding
    └─→ Medium difficulty

castleMoveIfLegal
    ├─→ Castling-specific logic
    └─→ Medium difficulty
```

### 3. Proof Pattern Opportunities
- **foldr membership patterns**: Once proven for pawns, reusable for king/queen foldr operations
- **Path validation patterns**: Once proven for rooks/bishops, patterns transfer to completeness proofs
- **Board invariant patterns**: Game state machine reasoning could apply to other invariants

### 4. Recommended Start Points (in order)

**Option A: Quick Progress (Lower Effort)**
1. Consolidate enPassant axioms (1h, -1 axiom)
2. Prove castling logic (3-4h, -1 axiom)
3. Create path validation lemmas (2-3h, prep work)
4. **Subtotal**: 6-8 hours, 2 axioms eliminated

**Option B: Foundation Building (Higher Complexity)**
1. Consolidate enPassant axioms (1h, -1 axiom)
2. Create comprehensive path validation lemmas (3-4h, prep)
3. Prove path validation axioms (3-4h, -2 axioms)
4. **Subtotal**: 7-9 hours, 3 axioms eliminated (more scalable)

---

## Success Criteria for Phase 3

### Minimum Target
- Eliminate 2-3 axioms (54-56% total reduction)
- Consolidate duplicate enPassant axiom
- Establish proof patterns for downstream work

### Stretch Goal
- Eliminate 4-5 axioms (57-60% total reduction)
- Complete path validation proofs
- Begin move list membership or castling proofs

### Ideal (Phase 3 + Part of Phase 4)
- Eliminate 6 axioms (65% total reduction)
- Complete path validation, move list membership
- Set up move completeness proofs for Phase 4

---

## Key Files to Review Before Starting

1. `Chess/Game.lean` - GameState definition and movePiece
2. `Chess/Rules.lean` - Move generation and pieceTargets
3. `Chess/Movement.lean` - Geometric predicates and squaresBetween
4. `Chess/Spec.lean` - Current axiom definitions and partial theorems

---

## Notes on Complexity vs. Value

| Axiom | Complexity | Value | ROI | Recommended |
|-------|-----------|-------|-----|------------|
| enPassant_target_isEmpty | Medium | Medium | High | ✅ Phase 3A |
| castleMoveIfLegal | Medium | Medium | High | ✅ Phase 3B |
| Path validation | Medium-High | High | High | ✅ Phase 3B-C |
| Move list membership | High | Medium | Medium | 🟡 Phase 3C (optional) |
| Move completeness | Very High | Very High | Medium | Phase 4+ |

---

## Phase 3 Success: We Will Have

- ✅ Consolidated duplicate axioms
- ✅ Established reusable proof patterns
- ✅ 54-60% cumulative axiom elimination
- ✅ Clear roadmap for Phase 4 (move completeness)
- ✅ Better understanding of game state machine invariants
