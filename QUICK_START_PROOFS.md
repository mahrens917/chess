# Quick Start: Completing Sub-case Proofs

This is a practical guide for completing individual `moveToSAN_unique` sub-cases.

---

## How to Work on a Sub-case

### 1. Choose a Sub-case
Pick from **easiest first** (to build momentum):
- `san_unique_castle_vs_ncastle` (30m) ← Start here!
- `san_unique_ncastle_vs_castle` (30m)
- `san_unique_pawn_advance_vs_capture` (1-2h)
- `san_unique_different_pieces` (1-2h)
- `square_algebraic_injective` (2-3h) ← Needed by others
- `san_unique_both_castles` (1-2h)
- `san_unique_both_pawn_advances` (2-3h)
- `san_unique_both_pawn_captures` (2-3h)
- `san_unique_pawn_vs_piece` (1-2h)
- `san_unique_piece_vs_pawn` (1-2h)
- `san_unique_same_piece_diff_dest` (1-2h)
- `san_unique_same_piece_same_dest` (3-4h) ← Hardest, do last

### 2. Find the Lemma

Open `Chess/ParsingProofs.lean` and search for the lemma name.

Example: `san_unique_castle_vs_ncastle` is at line 1375.

### 3. Understand the Proof Strategy

Read the docstring. It explains:
- What the lemma proves
- How to prove it
- Which helper lemmas to use
- Whether MCP `solve` can help

Example from `san_unique_castle_vs_ncastle`:
```lean
/-- Sub-case 2a: m1 is castle, m2 is not
    moveToSanBase m1 starts with "O", moveToSanBase m2 does not.
    This contradicts h_san_eq.
-/
```

### 4. Replace `sorry` with Proof

Change this:
```lean
lemma san_unique_castle_vs_ncastle (gs : GameState) (m1 m2 : Move)
    (h1_castle : m1.isCastle) (h2_not_castle : ¬m2.isCastle)
    (h_san_eq : moveToSanBase gs m1 = moveToSanBase gs m2) :
    MoveEquiv m1 m2 := by
  sorry -- TODO: Show contradiction: "O" prefix vs no "O" prefix
```

To this (example for castle case):
```lean
lemma san_unique_castle_vs_ncastle (gs : GameState) (m1 m2 : Move)
    (h1_castle : m1.isCastle) (h2_not_castle : ¬m2.isCastle)
    (h_san_eq : moveToSanBase gs m1 = moveToSanBase gs m2) :
    MoveEquiv m1 m2 := by
  -- moveToSanBase m1 starts with "O" (from castle branch)
  simp [moveToSanBase, h1_castle] at h_san_eq
  -- moveToSanBase m2 doesn't start with "O" (from non-castle branch)
  simp [moveToSanBase, h2_not_castle] at h_san_eq
  -- Extract from the definition to get contradiction
  sorry -- TODO: Your proof here
```

### 5. Test Your Work

```bash
# Check if it compiles
lake build

# Run tests to make sure nothing broke
lake test

# If compilation fails, read error carefully
# Lean will tell you exactly what type it expects
```

### 6. Commit Your Work

```bash
git add Chess/ParsingProofs.lean
git commit -m "Prove san_unique_castle_vs_ncastle sub-case"
```

---

## Using the `moveToSanBase` Definition

When you need to understand what `moveToSanBase` produces, look at `Chess/Parsing.lean` lines 317-330:

```lean
def moveToSanBase (gs : GameState) (m : Move) : String :=
  if m.isCastle then
    if m.toSq.fileNat = 6 then "O-O" else "O-O-O"
  else
    let capture := m.isCapture || m.isEnPassant
    if m.piece.pieceType = PieceType.Pawn then
      let pre := if capture then String.singleton m.fromSq.fileChar else ""
      let sep := if capture then "x" else ""
      pre ++ sep ++ m.toSq.algebraic ++ promotionSuffix m
    else
      let pre := pieceLetter m.piece.pieceType
      let dis := sanDisambiguation gs m
      let sep := if capture then "x" else ""
      pre ++ dis ++ sep ++ m.toSq.algebraic ++ promotionSuffix m
```

**Key takeaways:**
- Castles: "O-O" or "O-O-O" (determined by destination file)
- Pawns: No piece letter, optional file+x for capture
- Other pieces: Piece letter + disambiguation + optional x + destination + promotion

---

## Common Proof Patterns

### Pattern 1: String Contradiction

**When:** Proving two SANs differ (e.g., "O-O" ≠ "Qe4")

**How:**
```lean
-- Simplify both sides using moveToSanBase definition
simp [moveToSanBase, h_castle_1] at h_san_eq
simp [moveToSanBase, h_not_pawn_2] at h_san_eq
-- Now h_san_eq says something like "O-O" = "Qe4"
-- This is syntactically false - contradiction follows
contradiction
```

### Pattern 2: Extracting Components

**When:** Proving SANs match ⇒ components match

**How:**
```lean
-- h_san_eq : san1 = san2
-- Need to show: component1 = component2

-- Method: Show that san format determines component
have h_component : san1.get! position = san2.get! position := by
  rw [h_san_eq]

-- Then extract meaning from characters
have h_meaning : interpretation(san1.get! position) = ... := by
  sorry -- Usually decidable by character comparison
```

### Pattern 3: Using Helper Lemmas

**When:** Proving injectivity (e.g., same SAN ⇒ same piece type)

**How:**
```lean
-- We have: pieceLetter m1.pieceType = pieceLetter m2.pieceType
-- We want: m1.pieceType = m2.pieceType

have h_piece_eq : m1.piece.pieceType = m2.piece.pieceType := by
  apply pieceLetter_injective
  -- Justify the letter equality
  sorry

-- Now use the equality in the conclusion
exact ⟨..., h_piece_eq, ...⟩
```

---

## When to Use MCP `solve`

### Good candidates:
- `square_algebraic_injective` - Character arithmetic
- `san_unique_both_castles` - String pattern matching
- `san_unique_same_piece_same_dest` - Disambiguation arithmetic
- `san_unique_both_pawn_captures` - File-rank number extraction

### How to use:

1. **Get the goal:**
   ```lean
   -- Place cursor on `sorry` and check what Lean expects
   sorry -- at this point, need to prove: m1 = m2
   ```

2. **Create a minimal example:**
   ```
   I need to prove that if two moves are castles with the same SAN string,
   they're equivalent. Available helper lemmas:
   - castle_destination_determines_side: shows file 6 ↔ ¬file 2
   - moveToSanBase definition: castles produce "O-O" or "O-O-O" based on file

   Goal: m1.isCastle → m2.isCastle → moveToSanBase gs m1 = moveToSanBase gs m2 →
         m1.toSq.fileNat = m2.toSq.fileNat → MoveEquiv m1 m2
   ```

3. **Send to MCP `solve`**:
   Use the task tool with subagent_type='solve' and paste your goal

4. **Copy the returned proof** verbatim into your lemma

---

## Debugging Tips

### Build Fails: "Type Mismatch"

**Problem:**
```
type mismatch
  someProof
has type
  P : Prop
but is expected to have type
  Q : Prop
```

**Solution:** Reread the lemma type signature and what Lean expects. You might be proving the wrong thing.

### Build Fails: "Unknown Identifier"

**Problem:**
```
unknown identifier 'moveToSanBase'
```

**Solution:** You might be in the wrong namespace. Add `open Parsing` if needed.

### Test Fails: One Test Suite Fails

**Problem:**
```
[FAIL] SAN/PGN basics
```

**Solution:** Your proof might have introduced a logical error. Check that you didn't accidentally prove something false.

**Debug:**
```bash
lake test 2>&1 | grep -A 20 "FAIL"
```

---

## Examples: Working Through a Sub-case

### Example 1: `san_unique_castle_vs_ncastle` (Easy, 30m)

**Current code:**
```lean
lemma san_unique_castle_vs_ncastle (gs : GameState) (m1 m2 : Move)
    (h1_castle : m1.isCastle) (h2_not_castle : ¬m2.isCastle)
    (h_san_eq : moveToSanBase gs m1 = moveToSanBase gs m2) :
    MoveEquiv m1 m2 := by
  sorry -- TODO: Show contradiction: "O" prefix vs no "O" prefix
```

**Proof strategy:**
1. m1 is castle → moveToSanBase m1 produces "O-O" or "O-O-O"
2. m2 is not castle → moveToSanBase m2 doesn't start with "O"
3. These formats can't be equal
4. Contradiction to h_san_eq

**Proof:**
```lean
lemma san_unique_castle_vs_ncastle (gs : GameState) (m1 m2 : Move)
    (h1_castle : m1.isCastle) (h2_not_castle : ¬m2.isCastle)
    (h_san_eq : moveToSanBase gs m1 = moveToSanBase gs m2) :
    MoveEquiv m1 m2 := by
  -- If m2 is not castle, moveToSanBase m2 doesn't produce "O-O" or "O-O-O"
  -- But m1 is castle, so moveToSanBase m1 = "O-O" or "O-O-O"
  -- This contradicts h_san_eq
  -- We can derive False and use exfalso
  exfalso
  -- Unroll moveToSanBase for m1 (castle)
  unfold moveToSanBase at h_san_eq
  simp [h1_castle] at h_san_eq
  -- h_san_eq now says something like "O-O" = moveToSanBase gs m2
  -- But m2 not castle, so moveToSanBase m2 starts differently
  simp [moveToSanBase, h2_not_castle] at h_san_eq
  -- Should get contradiction from comparing "O-O" with non-"O" string
  omega  -- or `exact h_san_eq.symm ▸ sorry`
```

### Example 2: `san_unique_different_pieces` (Medium, 1-2h)

**Sketch:**
- Both non-pawn pieces, different types (e.g., Q vs R)
- moveToSanBase starts with pieceLetter for each
- pieceLetter Q ≠ pieceLetter R
- So SANs can't be equal
- Contradiction

**Proof:**
```lean
lemma san_unique_different_pieces (gs : GameState) (m1 m2 : Move)
    (h1_legal : m1 ∈ Rules.allLegalMoves gs)
    (h2_legal : m2 ∈ Rules.allLegalMoves gs)
    (h1_piece : m1.piece.pieceType ≠ PieceType.Pawn)
    (h2_piece : m2.piece.pieceType ≠ PieceType.Pawn)
    (h_types_diff : m1.piece.pieceType ≠ m2.piece.pieceType)
    (h_san_eq : moveToSanBase gs m1 = moveToSanBase gs m2) :
    MoveEquiv m1 m2 := by
  -- moveToSanBase for non-pawns starts with pieceLetter
  exfalso
  unfold moveToSanBase at h_san_eq
  simp [h1_piece, h2_piece] at h_san_eq
  -- h_san_eq now shows piece letters must be equal
  -- But pieceLetter_injective says equal letters ⇒ equal types
  have : m1.piece.pieceType = m2.piece.pieceType := by
    -- Extract first character of each side and use pieceLetter_injective
    sorry
  exact h_types_diff this
```

---

## Next Steps

1. **Pick `san_unique_castle_vs_ncastle`** as your first proof (30 minutes)
2. **Follow the example above** to complete it
3. **Test:** `lake build && lake test`
4. **Commit:** Document what you proved
5. **Move to next sub-case:** Use similar techniques

---

## Common Mistakes to Avoid

1. **Forgetting `exact` or `apply`** - Lean won't auto-apply lemmas
2. **Not unfolding definitions** - Use `unfold moveToSanBase` when needed
3. **Assuming too much** - Each `sorry` is a new proof, not continuation of previous
4. **String manipulation errors** - Double-check character positions and string concatenation
5. **Forgetting `h_san_eq` or other hypotheses** - You have assumptions; use them!

---

## When You Get Stuck

1. **Check the type signature** - What exactly are you trying to prove?
2. **Look at similar proven lemmas** - E.g., `pieceLetter_injective` if you're proving injectivity
3. **Try MCP `solve`** - Paste the goal and context, see if it helps
4. **Ask for help** - This is collaborative work; don't spend hours stuck

---

**Good luck! Pick the easy one first to build momentum. 🚀**
