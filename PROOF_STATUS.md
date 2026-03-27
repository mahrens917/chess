# Proof Status Tracker

**Last Updated:** 2026-03-26
**Lean Version:** 4.29.0-rc8 (with Mathlib)

## Current Metrics

| Metric | Count | Notes |
|--------|-------|-------|
| Total Sorries | 10 | Down from 11 at session start |
| Total Axioms | 7 | 1 original + 5 Lean 4.29 stdlib bridges + 1 game validity |
| Proven Theorems/Lemmas | 908 | Up from 488 at session start |
| Test Suites Passing | 21/21 | 100% |
| Slow Tests Passing | 7/7 | 100% |
| Build Status | Clean | Lean 4.29 + Mathlib |

---

## Remaining Sorries (10)

### Category 1: extractSanBase String Processing (4 sorries)

**File:** `Chess/Parsing_SAN_Proofs.lean`

These all need `String.trim` and `String.replace` identity on SAN character strings. The theorems EXIST in `Chess.StringLemmas` (namespace: `Chess.StringLemmas.String.*`) but agents working in worktrees couldn't access them because worktrees were created from old commits.

1. **Line 1064**: `parseSanToken_succeeds_on_moveToSAN` non-castle case
   - Needs: moveToSanBase output has no whitespace/dots
   - Use: `Chess.StringLemmas.String.trim_eq_self_of_no_whitespace` + `Chess.StringLemmas.String.replace_ep_dot_eq_self`

2. **Line 1113**: `parseSanToken_extracts_moveToSanBase` non-castle case
   - Same dependency as #1

3. **Line 1555**: `moveFromSanToken_finds_move`
   - Needs SAN injectivity (filter produces singleton)
   - Depends on SanUniquenessFullProof completion

4. **Line 1679**: `parseSanToken_normalizes_castling` error case
   - Needs: '0' survives trim+replace for arbitrary strings
   - Use: `Chess.StringLemmas.String.trim_preserves_non_ws_char` + replace char survival

### Category 2: SAN String Decomposition (6 sorries)

**File:** `Chess/SanUniquenessFullProof.lean`

The major proofs (piece decomposition, disambiguation, capture/EP) are DONE. What remains is pawn-specific geometry:

5-10. **Lines 1654-1765**: Pawn fromSq sub-cases
   - Non-Pawn pieceType impossibility (need: pieceTargets preserves piece field)
   - Forward pawn file equality (need: squareFromInts preserves file)
   - Blocking argument (need: single-step source blocks double-step)
   - Capture moves have isCapture=true (need: trace constructor)

---

## Axioms (7)

| Axiom | Category | Notes |
|-------|----------|-------|
| `allLegalMoves_nodup` | Chess structural | Needs sliding piece walk induction |
| `mem_allLegalMoves_implies_not_king_destination` | Game validity | Needs ValidGameState precondition |
| `String.replace_eq_intercalate_splitOn` | Lean stdlib | Classical replace = splitOn + intercalate |
| `string_any_eq_legacy` | Lean 4.29 bridge | New API → old API |
| `string_contains_eq_legacy` | Lean 4.29 bridge | New API → old API |
| `string_dropRight_eq_legacy` | Lean 4.29 bridge | New API → old API |
| `string_trim_eq_legacy` | Lean 4.29 bridge | New API → old API |

---

## What Was Proved This Session

### Major Theorems
- `moveFromSAN_moveToSAN_roundtrip` — SAN parse/generate roundtrip
- `moveToSAN_unique_full` — SAN injectivity (castle case)
- `base_eq_of_moveToSAN_eq` — equal moveToSAN implies equal base
- `non_castle_moveEquiv` — piece decomposition, disambiguation, capture/EP (3 of 4 cases)
- `same_color_bishops_dead` — dead position (fixed false statement)
- `deadPosition_sound_aux` — dead position soundness (fixed false statement)
- All 8 move generation structural lemmas
- `String.trim_preserves_non_ws_char` — byte-level proof
- `String.replace_ep_dot_eq_self` — via splitOn bridge
- `endsWith_ep_false_of_no_p` — custom meta-programming tactic
- `algebraic_injective`, `pieceLetter_injective`, `fileChar_injective` — via native_decide
- `noncastle_legal_castle_none` — castle field nullity (~300 lines)
- `intercalate_foldl` — String.intercalate structural decomposition

### Infrastructure Built
- ~6,000 lines of proof added
- 2 new proof files (SanUniquenessProof.lean, SanUniquenessFullProof.lean)
- String byte-level reasoning (trim, replace, splitOn, endsWith, extract)
- Custom `unfold_substrEq_loop` tactic for private Lean definitions
- Move generation tracing (walk, filterMap, pieceTargets, castleMoveIfLegal)
- Character class analysis for SAN notation

---

## Key Technical Notes

### Namespace Issue
String lemmas are in `Chess.StringLemmas.String.*` namespace. To use:
```lean
open Chess.StringLemmas in
-- or use Chess.StringLemmas.String.replace_ep_dot_eq_self
```

### Worktree Issue
Agent worktrees were created from old commits, not current HEAD. Future agents should either:
1. Run WITHOUT worktree isolation (to access accumulated changes)
2. Or ensure worktrees are created from current HEAD

### Lean 4.29 API Changes
- `String.trim` → `String.trimAscii` (returns Slice, deprecated)
- `s.trimAscii.toString = s.trim` by `rfl`
- `String.dropRight` → `String.dropEnd` (returns Slice)
- `String.any`/`String.contains` reimplemented via iterators

---

## Verification Commands

```bash
grep -rn "sorry" Chess/*.lean | grep -v "^.*:.*--" | grep "sorry" | grep -v "\.bak" | wc -l
grep -rn "^axiom \|^private axiom " Chess/*.lean | wc -l
grep -rn "^theorem\|^lemma\|^private theorem\|^private lemma" Chess/*.lean | wc -l
lake build && lake test
```
