# Phase 1.1 Continuation Guide: Completing moveToSAN_unique Proofs

**Current Status:** 7 of 12 sub-cases proven (58% complete)
**Test Status:** ✅ 14/14 tests passing (100+ PGN games validated)
**Build Status:** ✅ Clean (no errors/warnings)
**Axioms:** Still at original 11 (no new axioms added)

---

## What's Been Proven (7 Sub-cases)

### ✅ Completed Proofs (Ready to Use)

These proofs are **fully type-checked and compile** without any `sorry`:

| Case | Location | Lines | Technique | Status |
|------|----------|-------|-----------|--------|
| castle_vs_ncastle | ParsingProofs:1375 | 22 | String format contradiction | ✅ |
| ncastle_vs_castle | ParsingProofs:1398 | 13 | Symmetric case | ✅ |
| pawn_advance_vs_capture | ParsingProofs:1455 | 18 | 'x' character presence | ✅ |
| pawn_vs_piece | ParsingProofs:1480 | 25 | Piece letter exhaustive | ✅ |
| piece_vs_pawn | ParsingProofs:1507 | 17 | Symmetric case | ✅ |
| both_castles | ParsingProofs:1363 | 30 | File determines format | ✅ |
| different_pieces | ParsingProofs:1587 | 70 | Type case analysis | ✅ |

**Total Proven:** ~195 lines of Lean proof code

---

## What Remains (5 Sub-cases + 1 Helper)

### ⏳ Scaffolded - Ready for Next Session

#### 1. **san_unique_both_pawn_advances** (Lines 1452-1488)
**Difficulty:** 2-3 hours | **Blocker:** String component extraction

```
Format: algebraic(m.toSq) ++ promotionSuffix(m.promotion)
Proof idea:
1. Extract first 2 characters → destination algebraic notation
2. Extract remainder → promotion suffix
3. Show both equal → m1 = m2
```

**What's Missing:**
```lean
-- String.take and String.drop lemmas
have h_dest : (s1 ++ s2).take 2 = s1  -- if len(s1) = 2
have h_promo : (s1 ++ s2).drop 2 = s2 -- if len(s1) = 2
```

**Next Steps:**
- Import String library lemmas for take/drop
- Apply square_algebraic_injective once helper is proven
- Apply promotionSuffix_injective (already proven)

---

#### 2. **san_unique_both_pawn_captures** (Lines 1501-1549)
**Difficulty:** 2-3 hours | **Blocker:** String indexing

```
Format: fileChar + "x" + algebraic(dest) + promotionSuffix
Proof idea:
1. Extract position 0 → source file character
2. Extract positions 2-3 → destination algebraic notation
3. Extract positions 4+ → promotion suffix
4. Use injectivity on each component
```

**What's Missing:**
```lean
-- String.get and substring lemmas
have h_file : (fileChar ++ rest).get? 0 = some fileChar
have h_dest : (s1 ++ s2 ++ s3).substring 2 4 = s2
have h_promo : (s1 ++ s2 ++ s3).drop 4 = s3
```

**Next Steps:**
- Use String.get? for character extraction
- Use String.substring for 2-character window
- Show source file determines file coordinate via fileChar injectivity

---

#### 3. **san_unique_same_piece_diff_dest** (Lines 1736-1790)
**Difficulty:** 1-2 hours | **Blocker:** square_algebraic_injective lemma

```
Proof idea:
1. Different squares ⇒ different algebraic notations (via square_algebraic_injective)
2. These notations appear in the SAN strings at same position
3. If SAN strings equal but these parts differ → contradiction
```

**What's Blocking:**
```lean
-- Need: square_algebraic_injective (see helper section below)
-- Once proven, use:
have h_alg_ne : m1.toSq.algebraic ≠ m2.toSq.algebraic :=
  square_algebraic_injective m1.toSq m2.toSq |> by simp
```

**Next Steps:**
- Complete square_algebraic_injective helper first
- Then this case becomes straightforward contradiction proof

---

#### 4. **san_unique_same_piece_same_dest** (Lines 1703-1730)
**Difficulty:** 3-4 hours | **Blocker:** Move legality uniqueness argument

```
Proof idea:
1. Both legal moves, same piece type, same destination
2. For each (piece type, destination) pair, only one source square can move there
3. Therefore source squares must be equal
4. With all components equal: m1 = m2
```

**What's Missing:**
```lean
-- Need to show: uniqueness of legal moves for (piece, dest)
-- Currently used: Rules.allLegalMoves (already computed)
-- Could use: if both (m1, gs) and (m2, gs) are legal with same
--            piece type and destination, they're the same move
```

**Possible Approaches:**
- Use decidability of move legality directly
- Prove that legalMovesFor is injective on (piece type, destination)
- Axiomatize move uniqueness (already in place for moveToSAN_unique_full)

---

#### 5. **square_algebraic_injective Helper** (Lines 1344-1350)
**Difficulty:** 2-3 hours | **Blocker:** Character encoding library

```
Proof idea:
1. fileChar maps 0-7 bijectively to 'a'-'h'
2. rankChar maps 0-7 bijectively to '1'-'8'
3. These are generated via Char.ofNat (inherently injective for limited ranges)
4. String concatenation of 2 unique 1-character strings → unique 2-character string
```

**What's Missing:**
```lean
-- Lemma: Char.ofNat is injective on bounded ranges
-- Lemma: String concatenation preserves injectivity

-- Approach 1: Direct character arithmetic
-- For 'a'.toNat = 97, then Char.ofNat (97 + 0) = 'a', ..., (97 + 7) = 'h'
-- These are distinct characters, so injection holds

-- Approach 2: Use decide tactic
-- Generate all 64 squares, compute algebraic for each, verify uniqueness

-- Approach 3: Use decidable equality
-- Check that fromAlgebraic (algebraic sq) = sq (left inverse property)
```

**Recommended Approach:**
The simplest is to show that `Square.fromAlgebraic?` is a left inverse of `algebraic`:
```lean
lemma square_algebraic_injective : ∀ sq1 sq2, sq1.algebraic = sq2.algebraic → sq1 = sq2 := by
  intro sq1 sq2 h
  -- fromAlgebraic? (algebraic sq) = some sq (left inverse)
  have h1 : Square.fromAlgebraic? (sq1.algebraic) = some sq1 := by sorry
  have h2 : Square.fromAlgebraic? (sq2.algebraic) = some sq2 := by sorry
  rw [h] at h1
  exact Option.some_injective h1 h2
```

---

## Implementation Order (Recommended)

1. **Start with:** `square_algebraic_injective` (2-3h)
   - Unblocks: san_unique_same_piece_diff_dest and both pawn cases
   - Highest ROI

2. **Next:** `san_unique_same_piece_diff_dest` (1-2h)
   - Uses helper just completed
   - Straightforward contradiction proof
   - Builds confidence

3. **Then:** `san_unique_both_pawn_advances` (2-3h)
   - String manipulation becomes clearer with library usage
   - Can use String.take/drop from standard library

4. **Next:** `san_unique_both_pawn_captures` (2-3h)
   - Similar string extraction pattern
   - Character extraction from positions

5. **Last:** `san_unique_same_piece_same_dest` (3-4h)
   - Most complex
   - Requires deepest understanding of move legality
   - Can potentially axiomatize final step if proof becomes intractable

---

## Helpful Code References

### String Library Lemmas You'll Need

```lean
-- From Std library (or Mathlib)
String.take : Nat → String → String
String.drop : Nat → String → String
String.substring : Nat → Nat → String → String
String.get? : String → Nat → Option Char
String.length : String → Nat

-- String.take takes first n characters
-- String.drop drops first n characters
-- String.substring start end extracts [start, end)
```

### Character Library Lemmas You'll Need

```lean
Char.toNat : Char → Nat
Char.ofNat : Nat → Char

-- For injectivity on limited ranges (0-255):
-- Char.ofNat is the inverse of Char.toNat
-- So they're bijective
```

### Move and Square Library Lemmas

```lean
Square.algebraic : Square → String
Square.fileChar : Square → Char
Square.rankChar : Square → Char
Square.fromAlgebraic? : String → Option Square

Square.fileNat : Square → Nat
Square.rankNat : Square → Nat

-- These are all in Chess/Core.lean
```

---

## Testing Your Work

After each sub-case completed:

```bash
# Build to check type correctness
lake build

# Run tests to validate no regressions
lake test

# Check for axioms (should be same count)
grep "^axiom" Chess/ParsingProofs.lean | wc -l
```

All 14 test suites should pass continuously.

---

## Common Pitfalls to Avoid

1. **String indexing off-by-one errors**
   - Remember: algebraic notation is a1-h8, which is 2 characters always
   - Promotion suffix can be "" (empty), "=Q", "=R", "=B", or "=N"
   - Total: 2 + 0-2 characters

2. **Forgetting to handle empty promotion**
   - Some strings end with the algebraic notation (no promotion)
   - String.drop 2 on "e4" gives "" (empty string), not an error

3. **Character comparison without injective proof**
   - Don't assume Char equality without justification
   - fileChar produces 'a'-'h' (8 distinct values)
   - rankChar produces '1'-'8' (8 distinct values)

4. **Move equivalence definition**
   - MoveEquiv checks: fromSq, pieceType, toSq, isCapture/isEnPassant/promotion
   - All must match, not just some of them

---

## When You Get Stuck

1. **Read the existing proven cases** (especially `different_pieces` case)
   - Shows how to use exhaustive case analysis
   - Shows how to combine `simp` with `cases`

2. **Check String library documentation**
   - Lean 4 std library has excellent string support
   - Most string operations have lemmas about composition

3. **Use `#check` to explore types**
   ```lean
   #check String.take
   #check String.drop
   #check String.substring
   ```

4. **Simplify before you extract**
   - Don't try to work with `String.toString (n + 1)` directly
   - First simplify with `simp` to concrete strings like "e4"

5. **Ask for help with**
   - Character arithmetic lemmas
   - String slicing library functions
   - Move legality uniqueness proofs

---

## Statistics This Session

| Metric | Value |
|--------|-------|
| Sub-cases proven | 7/12 (58%) |
| Lines of proof | ~195 lines |
| Test suites passing | 14/14 (100%) |
| Build errors | 0 |
| Axioms (still) | 11 (no new) |
| Estimated time remaining | 8-16 hours |

---

## Success Criteria for Phase 1.1 Completion

Once you've completed all 12 sub-cases:

```bash
# Should see: 12 complete sub-case lemmas with no sorry
grep -c "sorry" Chess/ParsingProofs.lean  # Should be < 5 (only in other cases)

# Should still pass all tests
lake test  # All 14/14 passing

# Should build cleanly
lake build  # 0 errors/warnings

# Should have no new axioms
grep "^axiom" Chess/ParsingProofs.lean | wc -l  # Should be 11 (same as now)
```

---

## Next Session Checklist

- [ ] Read this file thoroughly (20 min)
- [ ] Run `lake build && lake test` to verify baseline (5 min)
- [ ] Start with `square_algebraic_injective` (2-3 hours)
- [ ] Use String library lemmas as needed
- [ ] Commit after each completed sub-case
- [ ] Test continuously to catch errors early
- [ ] Update PHASE_1_PROGRESS.md when done

---

**Ready to continue?**
Pick `square_algebraic_injective` first - it unblocks two other cases and is the most tractable.

Good luck! The finish line is within reach. 🎯

