# Axiom Elimination Plan

**Goal:** Reduce 16 axioms to 0.
**Approach:** 4 parallel workstreams, ordered by tractability.

---

## Workstream A: Lean 4.29 API Bridges (3 axioms)

**Files:** Parsing_SAN_Proofs.lean
**Effort:** Low — these likely have existing proofs in Mathlib/Batteries
**Dependencies:** None
**Can run in parallel with:** Everything

### Axioms
1. `String.front_eq_head` — `s.front = s.toList.head`
2. `String.back_eq_getLast` — `s.back = s.toList.getLast`
3. `String.all_ofList` — `(String.ofList l).all p = l.all p`

### Strategy
Search Mathlib and Batteries for existing proofs:
```bash
grep -rn "front.*head\|front.*toList" .lake/packages/batteries/
grep -rn "back.*getLast\|back.*toList" .lake/packages/batteries/
grep -rn "all_ofList\|all.*toList" .lake/packages/batteries/
```

If not found, prove via `unfold String.front/back` + `utf8GetAux` reasoning (similar infrastructure already exists in StringLemmas.lean Section 14).

---

## Workstream B: Lean 4.29 Stdlib Bridges (5 axioms)

**Files:** StringLemmas.lean
**Effort:** Medium — need to show new API = old API
**Dependencies:** None
**Can run in parallel with:** Everything

### Axioms
4. `string_any_eq_legacy` — new `String.any` = `String.Legacy.any`
5. `string_contains_eq_legacy` — new `String.contains` = `String.Legacy.contains`
6. `string_dropRight_eq_legacy` — new `String.dropRight` = old implementation
7. `string_trim_eq_legacy` — new `String.trim` = old `Substring.Raw.trim`
8. `String.replace_eq_intercalate_splitOn` — `replace` = `intercalate ∘ splitOn`

### Strategy
For 4-7: The new functions go through `String.Slice`/`Std.Iterators`. Two approaches:
- **Approach 1:** Check if `String.Legacy.*` functions have `@[simp]` lemmas connecting them to the new API in Batteries
- **Approach 2:** Prove by showing both functions compute the same result on `String.toList` — unfold both to their byte-level implementations and show they traverse the same characters

For 8: `String.replace` uses KMP-based `ForwardSliceSearcher`. Prove by:
- Showing `splitOn` and `replace` use the same pattern-matching algorithm
- Or proving via `String.splitOn` characterization + `intercalate` reassembly

### Key insight
`String.Legacy.any` IS the old `String.any` — it was preserved in Batteries when the new API was introduced. If Batteries has `@[deprecated_alias]` or `theorem String.any_eq_legacy`, use that directly.

---

## Workstream C: SAN Character Properties (6 axioms)

**Files:** Parsing_SAN_Proofs.lean
**Effort:** Medium-High — systematic but repetitive case analysis
**Dependencies:** Workstreams A & B help but aren't strictly required
**Can run in parallel with:** A, B, D

### Axioms
9. `parseSanToken_succeeds_non_castle` — extractSanBase succeeds on non-castle moveToSAN
10. `parseSanToken_extracts_non_castle` — extractSanBase recovers moveToSanBase
11. `extractSanBase_ne_error` — extractSanBase succeeds when token has '0'
12. `replace_ep_dot_preserves_zero` — '0' survives `String.replace "e.p." ""`
13. `dropEnd_ep_preserves_zero` — '0' survives `String.dropEnd 2`
14. `moveFromSanToken_finds_move` — SAN filter produces matching move

### Strategy

**Phase C1: Character lemmas (12, 13)**
Prove '0' survives `replace` and `dropEnd`:
- For 12: Use `replace_eq_intercalate_splitOn` (axiom 8). `splitOn "e.p."` splits on the pattern. `intercalate ""` joins the parts. '0' ∉ "e.p.".toList, so '0' stays in one of the parts. Need: `List.mem_join_of_mem` or similar from Mathlib.
- For 13: `dropEnd 2` removes last 2 chars. When `endsWith "ep"`, the last 2 are 'e','p'. Since '0' ≠ 'e' and '0' ≠ 'p', '0' is in the prefix. Prove via `List.dropLast` reasoning.

**Phase C2: extractSanBase pipeline (11)**
With 12 and 13 proved, `extractSanBase_ne_error` follows from the already-proved list-level pipeline lemmas (`peelAnnotations_preserves_zero`, `dropWhile_plus_preserves_zero`, etc.).

**Phase C3: moveToSanBase character analysis (9, 10)**
Prove every character in `moveToSanBase gs m` (non-castle) is from {a-h, 1-8, K,Q,R,B,N,x,=,O,-}:
- `pieceLetter pt` ∈ {"K","Q","R","B","N",""} — 6 cases by `cases pt`
- `sanDisambiguation gs m` — chars are `fileChar` (a-h) or `rankChar` (1-8)
- `algebraic sq` — `fileChar` + `rankChar`
- `promotionSuffix m` ∈ {"","=Q","=R","=B","=N"} — 5 cases
- `"x"` — single char

Then show: none of these chars are whitespace, '.', or 'p'. Use `native_decide` for each concrete char.

From these character properties:
- `String.trim_eq_self_of_no_whitespace` applies → trim is identity
- `String.replace_ep_dot_eq_self` applies → replace is identity
- `endsWith_ep_false_of_no_p` applies → no dropEnd
- Trace through extractSanBase → .ok with correct base

**Phase C4: SAN filter (14)**
`moveFromSanToken_finds_move` needs: the filter over legal moves matching a SAN token produces at least one result equivalent to `m`. This follows from SAN uniqueness (largely proved in SanUniquenessFullProof.lean). May need the pawn fromSq sub-proofs to be completed first.

---

## Workstream D: Chess-Structural (2 axioms)

**Files:** PerftProofs.lean, KMinorMoveLemmas.lean
**Effort:** High
**Dependencies:** None
**Can run in parallel with:** Everything

### Axioms
15. `allLegalMoves_nodup` — move generation produces no duplicates
16. `mem_allLegalMoves_implies_not_king_destination` — no legal move captures a king

### Strategy

**For 15 (`allLegalMoves_nodup`):**
Previous attempts proved King and Knight cases. Remaining:
- **Sliding pieces** (Queen/Rook/Bishop): Prove `walk` visits distinct squares per ray direction. Each step increments file/rank by the delta, producing distinct `(file,rank)` pairs. Different rays have different delta directions → different target squares.
- **Pawns**: Forward moves have distinct ranks (single vs double step → different `toSq`). Captures have distinct files. Promotions differ by `promotion` field.
- **Precondition**: May need `hasValidKings` (at most one king per color) to avoid duplicate castle moves.

**For 16 (`mem_allLegalMoves_implies_not_king_destination`):**
This requires proving that in a legal chess position, no legal move can capture a king. The issue: `GameState` doesn't enforce position validity. Two options:
- **Option A:** Add `ValidGameState` hypothesis (position reachable from start)
- **Option B:** Prove it from `basicLegalAndSafe` — if the opponent's king could be captured, the opponent was already in check and shouldn't have been allowed to move. This requires showing the previous move was legal, which needs game history.

Recommendation: Option A with a `ValidGameState` predicate.

---

## Execution Order

```
Week 1 (parallel):
  ├── Workstream A: Search Mathlib/Batteries for front/back/all_ofList [1 day]
  ├── Workstream B: Investigate Legacy bridges in Batteries [2-3 days]
  └── Workstream D: allLegalMoves_nodup sliding piece walk [3-5 days]

Week 2 (parallel):
  ├── Workstream C Phase C1-C2: '0' preservation lemmas [2 days]
  ├── Workstream C Phase C3: moveToSanBase char analysis [3-4 days]
  └── Workstream D: king destination (if Option A chosen) [2 days]

Week 3:
  └── Workstream C Phase C4: moveFromSanToken_finds_move [2-3 days]
      (depends on C3 completion)
```

---

## Parallel Agent Strategy

Launch these agent groups simultaneously:

### Group 1: Library Search (Workstreams A + B)
Search Mathlib/Batteries for existing proofs of the 8 stdlib bridge axioms. Many may already be proved upstream.

### Group 2: Character Analysis (Workstream C, Phases C1-C3)
Prove moveToSanBase character properties and '0' preservation. This is the largest workstream but highly parallelizable — each component (pieceLetter, algebraic, disambiguation, promotionSuffix) can be analyzed independently.

### Group 3: Move Generation (Workstream D)
Prove `allLegalMoves_nodup` for sliding pieces and pawns. Independent of all other workstreams.

### Group 4: Integration (Workstream C, Phase C4)
After Groups 1-3 complete, assemble the remaining axiom proofs.
