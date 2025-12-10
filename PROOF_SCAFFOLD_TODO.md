# Proof Scaffold Implementation TODO

**Goal:** Complete all remaining proofs to achieve 100% formal verification with 0 axioms.

**Status:** Foundation scaffold in place (moveToSAN_unique theorem structure + 7 sub-case lemmas defined). All cases tested compiles. Ready for incremental proof completion.

**Total Effort Estimate:** 25-40 hours (can be parallelized)

---

## Phase 1: Parser Uniqueness (Foundation) - 9-12 hours

### Phase 1.1: Prove `moveToSAN_unique` - 8-11 hours

**Status:** Scaffold complete, 12 sub-cases identified, ready for individual completion

**Sub-cases breakdown:**

#### HELPER LEMMAS (4 lemmas)

- [x] `pieceLetter_injective` - ✅ **COMPLETED** (lines 1321-1325)
  - Different piece types have different piece letters
  - Proof: Exhaustive case analysis over PieceType

- [ ] `square_algebraic_injective` (lines 1334-1340) - **TODO 2-3h**
  - Square algebraic notation uniquely identifies square
  - Current: `sorry` stub
  - Proof strategy: Extract file/rank characters, compare with Square fields
  - Can use: Character value comparison, Square construction injectivity

- [x] `castle_destination_determines_side` - ✅ **COMPLETED** (lines 1331-1332)
  - Castling destination file uniquely determines KS vs QS
  - Proof: Simple arithmetic (file=6 ↔ ¬file=2)

- [x] `promotionSuffix_injective` - ✅ **COMPLETED** (lines 1342-1352)
  - Promotion suffix uniquely encodes promotion piece
  - Proof: Case analysis + pieceLetter_injective

#### SUB-CASE LEMMAS (8 lemmas)

**Sub-case 1: Both Castles**
- [ ] `san_unique_both_castles` (lines 1363-1367) - **TODO 1-2h**
  - If both moves are castles with same SAN, they have same destination
  - Proof strategy: "O-O" vs "O-O-O" string comparison
  - Helper: castle_destination_determines_side
  - MCP `solve` candidate: String pattern matching

**Sub-case 2: Castles vs Non-Castles**
- [ ] `san_unique_castle_vs_ncastle` (lines 1375-1379) - **TODO 30m**
  - m1 castle, m2 not: "O" prefix vs no "O" → contradiction
  - Proof: Simple string prefix analysis
  - MCP `solve` candidate: String prefix contradiction

- [ ] `san_unique_ncastle_vs_castle` (lines 1382-1386) - **TODO 30m**
  - Symmetric to case 2a
  - Proof: Same as 2a, reversed roles

**Sub-case 3: Both Pawns**
- [ ] `san_unique_both_pawn_advances` (lines 1403-1411) - **TODO 2-3h**
  - Both pawns, no capture: "e4" + [=Q] format
  - Proof strategy:
    1. Extract destination square from SAN base (algebraic notation)
    2. Extract promotion from suffix (=Q, =R, =B, =N, or none)
    3. Use square_algebraic_injective and promotionSuffix_injective
    4. Conclude toSq and promotion match → MoveEquiv
  - MCP `solve` candidate: String suffix extraction, piece identification

- [ ] `san_unique_both_pawn_captures` (lines 1417-1425) - **TODO 2-3h**
  - Both pawns, both capture: "e"+"x"+"d4" + [=Q] format
  - Proof strategy:
    1. Extract source file from first character ('a'-'h')
    2. Extract destination square from SAN (skip source file and 'x')
    3. Extract promotion from suffix
    4. Source file uniquely identifies fromSq (rank is constrained by pawn position)
    5. Use square_algebraic_injective for destination
    6. Conclude MoveEquiv
  - Tricky: Source file → fromSq requires legality
  - MCP `solve` candidate: Pawn file-rank arithmetic

- [ ] `san_unique_pawn_advance_vs_capture` (lines 1431-1438) - **TODO 1-2h**
  - One pawn advance ("e4"), other capture ("exd4")
  - Proof: 'x' presence differs → contradiction to h_san_eq
  - MCP `solve` candidate: String character search ('x' membership)

**Sub-case 4: Pawn vs Non-Pawn**
- [ ] `san_unique_pawn_vs_piece` (lines 1446-1451) - **TODO 1-2h**
  - m1 pawn (no piece letter), m2 piece (Q/R/B/N/K)
  - Proof: SAN format differs → contradiction
  - MCP `solve` candidate: First character analysis (empty vs Q/R/B/N)

- [ ] `san_unique_piece_vs_pawn` (lines 1454-1459) - **TODO 1-2h**
  - Symmetric to case 4a
  - Proof: Same as 4a, reversed roles

**Sub-case 5: Both Piece Moves (Q/R/B/N/K)**
- [ ] `san_unique_different_pieces` (lines 1467-1475) - **TODO 1-2h**
  - Different piece types (Q vs R, etc.)
  - Proof: Piece letters differ → pieceLetter_injective → contradiction
  - Uses: pieceLetter_injective (already complete)
  - MCP `solve` candidate: First character extraction and comparison

- [ ] `san_unique_same_piece_same_dest` (lines 1481-1490) - **TODO 3-4h** ⭐ MOST COMPLEX
  - Same piece type, same destination, need disambiguation
  - Proof strategy:
    1. Extract piece type from first character (already matching by assumption)
    2. Extract destination from SAN (middle-ish part)
    3. Extract disambiguation info (file/rank characters for source)
    4. Disambiguation uniquely identifies source square (by definition in Parsing.lean lines 298-314)
    5. With piece type, fromSq, toSq matching → MoveEquiv
  - Most complex: disambiguation logic
  - Needs: Understanding of sanDisambiguation function behavior
  - MCP `solve` candidate: Disambiguation character extraction and interpretation

- [ ] `san_unique_same_piece_diff_dest` (lines 1496-1503) - **TODO 1-2h**
  - Same piece type, different destinations
  - Proof: Destinations differ in algebraic notation → contradiction via square_algebraic_injective
  - MCP `solve` candidate: Destination square extraction from SAN string

#### MAIN THEOREM

- [x] `moveToSAN_unique` - ✅ **COMPLETED** (lines 1529-1577)
  - Proof structure: Combines all sub-case lemmas via nested case analysis
  - Kernel logic in place
  - Depends on all 8 sub-case lemmas being proven

### Phase 1.2: Prove `moveToSAN_unique_full` - 1 hour

**Status:** Pending (depends on Phase 1.1 complete)

**File:** Chess/ParsingProofs.lean (lines 1579+)

- [ ] `moveToSAN_unique_full` (line ~1587) - **TODO 1h**
  - Full SAN (base + check/mate suffix) uniqueness
  - Proof strategy:
    1. Note: moveToSAN = moveToSanBase + suffix
    2. Suffix determined by game state alone (not move)
    3. If full SANs equal, bases must equal
    4. Apply moveToSAN_unique to bases
    5. Conclude MoveEquiv
  - Should be quick once moveToSAN_unique is proven
  - MCP `solve` candidate: String suffix analysis

---

## Phase 2: Parser Round-Trip Helpers - 7-10 hours

**Status:** Pending (depends on Phase 1.1)

**File:** Chess/Parsing_SAN_Proofs.lean (lines ~138-168)

Current axioms to eliminate:
- [ ] `parseSanToken_succeeds_on_moveToSAN` - **TODO 2-3h**
- [ ] `parseSanToken_extracts_moveToSanBase` - **TODO 2-3h**
- [ ] `legal_move_passes_promotion_rank_check` - **TODO 1-2h**
- [ ] `moveFromSanToken_finds_move` - **TODO 2-3h** (depends on moveToSAN_unique)

These enable the already-proven `moveFromSAN_moveToSAN_roundtrip` theorem.

---

## Phase 3: Move Generation Completeness - 4-6 hours

**Status:** Pending (independent of Phases 1-2)

**Files:**
- Chess/Rules.lean - add legalMove predicate
- Chess/Spec.lean - add completeness theorems

- [ ] Define `legalMove` predicate - **TODO 30m**
- [ ] Prove `legalMovesFor_complete` - **TODO 2-3h**
- [ ] Prove `allLegalMoves_complete` - **TODO 1-2h**
- [ ] Prove `allLegalMoves_sound` - **TODO 1h**
- [ ] Prove final biconditional: `legalMove ↔ ∈ allLegalMoves` - **TODO 30m**

---

## Phase 4: Perft Induction - 3-5 hours

**Status:** Pending (depends on Phase 1.1 for moveToSAN_unique_full)

**File:** Chess/PerftProofs.lean

Current axioms to eliminate:
- [ ] `perft_complete_succ` - **TODO 2-3h** (depends on moveToSAN_unique_full)
- [ ] `perft_foldl_count_correspondence` - **TODO 1-2h**
- [ ] `perft_bijective_san_traces_succ` - **TODO 30m** (once moveToSAN_unique_full proven)

---

## Phase 5: Dead Position Formalization - 2-6 hours

**Status:** Pending (independent of other phases)

**Files:**
- Chess/Rules.lean - add formalization
- Chess/DeadPositionProofs.lean - new file, dead position theorems
- Chess/SearchSpace.lean - fix FIDE citation

- [ ] Define `isDeadPosition` formally - **TODO 1h**
- [ ] Prove K vs K dead - **TODO 30m**
- [ ] Prove K+N vs K dead - **TODO 1h**
- [ ] Prove K+B vs K dead - **TODO 1h**
- [ ] Prove same-color bishops dead - **TODO 1h**
- [ ] Prove heuristic soundness - **TODO 1-2h**
- [ ] Document incompleteness - **TODO 30m**
- [ ] Fix SearchSpace FIDE citation - **TODO 15m**

---

## Phase 6: Testing & Validation - 1-2 hours

After completing other phases:

- [ ] Run `lake build` - verify 0 errors
- [ ] Run `lake test` - verify 14/14 suites pass
- [ ] Run `lake exe slowTests` - verify comprehensive tests pass
- [ ] Count axioms: `grep "^axiom" Chess/*.lean | wc -l` - should be 0
- [ ] Count sorries: `grep "sorry" Chess/*.lean | wc -l` - should be 0
- [ ] Count theorems: `grep -c "theorem\|lemma" Chess/*.lean` - should be 240+
- [ ] Update README.md - reflect 100% pure logical proofs, 0 axioms

---

## Implementation Priority & Parallelization

**Critical Path:**
1. Phase 1.1: moveToSAN_unique (prerequisite for 1.2, 2, 4)
2. Phase 1.2: moveToSAN_unique_full (prerequisite for 4)
3. Phase 2: Parser helpers
4. Phase 4: Perft (depends on 1.2)

**Can Run in Parallel (after Phase 1.1):**
- Phase 3: Move generation completeness (independent)
- Phase 5: Dead position formalization (independent)

**Recommended Order for Solo Work:**
1. Phase 1.1 - Foundation (8-11h)
2. Phase 1.2 - Quick win (1h)
3. Phase 3 - Independent, moderate (4-6h)
4. Phase 2 - Depends on 1.1, moderate (7-10h)
5. Phase 4 - Depends on 1.2, moderate (3-5h)
6. Phase 5 - Independent, last (2-6h)
7. Phase 6 - Wrap-up (1-2h)

---

## MCP `solve` Server Integration

The following sub-cases are good candidates for MCP solve:
- `square_algebraic_injective` - Character comparison and Square construction
- `san_unique_both_castles` - String pattern matching ("O-O" vs "O-O-O")
- `san_unique_castle_vs_ncastle` - String prefix analysis
- `san_unique_pawn_advance_vs_capture` - String character search ('x' membership)
- `san_unique_pawn_vs_piece` - First character type analysis
- `san_unique_different_pieces` - Piece letter extraction and comparison
- `san_unique_same_piece_same_dest` - Disambiguation character extraction (most complex)
- `san_unique_same_piece_diff_dest` - Destination square extraction

**Approach:** For each `sorry`, extract the proof goal and send to MCP solve with context of helper lemmas available.

---

## Success Criteria

✅ **Zero axioms** in all Chess/*.lean files
✅ **Zero sorries** in all Chess/*.lean files
✅ **All tests passing** (14/14 suites, 100+ PGN games)
✅ **Build clean** with no warnings
✅ **Documentation updated** - README reflects 100% pure logical proofs
✅ **Proof count:** 240+ theorems (current ~215 + new 25-30)

---

## Notes

- This TODO file is a living document - update as proofs complete
- Each sub-case is roughly 1-3 hours of focused proof work
- String manipulation proofs tend to be tedious but straightforward
- MCP `solve` can significantly reduce time on algebraic sub-goals
- Scaffold is clean and compiles - safe to work on individual sub-cases
- All test suites still passing with current scaffold
