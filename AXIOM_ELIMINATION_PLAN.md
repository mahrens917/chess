# Axiom Elimination Plan

**Current state:** 16 axioms, 0 sorries, 930 theorems (Lean 4.29 + Mathlib)

---

## Category 1: Lean 4.29 String API Bridges — BLOCKED upstream (5 axioms)

**Files:** StringLemmas.lean
**Status:** Unprovable in Lean 4.29. Requires upstream Lean/Batteries changes.

In Lean 4.29 the `String` type was rewritten from `{ data : List Char }` to a
validated UTF-8 `ByteArray`. All core String operations (`any`, `contains`,
`dropRight`, `trim`, `replace`) now use `String.Slice` + `String.Internal.*`
which are **opaque** — no specification theorems connect them to `List Char`.
The old implementations were preserved in `String.Legacy` (Batteries) but no
bridge lemmas exist.

Every approach was tried: `rfl`, `decide`, `native_decide`, `unfold`/`delta`,
`exact?`/`apply?`/`rw?`, and the `solve` MCP server. All fail because the
kernel cannot reduce the new opaque operations.

### Axioms

| # | Name | File:Line | Statement |
|---|------|-----------|-----------|
| 1 | `string_any_eq_legacy` | StringLemmas.lean:41 | `s.any p = String.Legacy.any s p` |
| 2 | `string_contains_eq_legacy` | StringLemmas.lean:51 | `s.contains c = String.Legacy.contains s c` |
| 3 | `string_dropRight_eq_legacy` | StringLemmas.lean:46 | `s.dropRight n = (toRawSubstring s \|>.dropRight n \|>.toString)` |
| 4 | `string_trim_eq_legacy` | StringLemmas.lean:57 | `s.trim = (Substring.Raw.trim (toRawSubstring s)).toString` |
| 5 | `String.replace_eq_intercalate_splitOn` | StringLemmas.lean:1017 | `s.replace pat rep = String.intercalate rep (s.splitOn pat)` |

### Unblock path
Upstream Lean or Batteries must provide:
1. Correctness theorem for `Std.Iter.any`/`Std.Iter.all` in terms of `Iter.toList`
2. Specification theorems for `String.Internal.any`, `.contains`, `.front`, `.back`, `.trim`
3. Bridge between `String.extract` (byte-level) and `String.Pos.Raw.extract` (list-level)

---

## Category 2: String-to-List Bridges — BLOCKED on Category 1 (3 axioms)

**Files:** Parsing_SAN_Proofs.lean
**Status:** Provable once Category 1 is resolved. Each reduces to a Category 1 axiom + a Batteries `String.Legacy.*` lemma.

| # | Name | File:Line | Statement |
|---|------|-----------|-----------|
| 6 | `String.front_eq_head` | Parsing_SAN_Proofs.lean:16 | `s.front = s.toList.head hlist` |
| 7 | `String.back_eq_getLast` | Parsing_SAN_Proofs.lean:20 | `s.back = s.toList.getLast _` |
| 8 | `String.all_ofList` | Parsing_SAN_Proofs.lean:26 | `(String.ofList l).all p = l.all p` |

### Proof sketch (verified, compiles with bridge axioms)
- Prove `string_front_eq_legacy` (new → Legacy), then compose with `String.front_eq` (Legacy → toList) from Batteries.
- Same pattern for `back` and `all`.

---

## Category 3: SAN Parsing Pipeline — BLOCKED on Categories 1-2 (5 axioms)

**Files:** Parsing_SAN_Proofs.lean
**Status:** Blocked by opaque `String.replace`, `String.endsWith`, `String.trim`, `String.dropEnd`.

| # | Name | File:Line | Statement |
|---|------|-----------|-----------|
| 9 | `replace_ep_dot_preserves_zero` | Parsing_SAN_Proofs.lean:36 | `'0' ∈ s.toList → '0' ∈ (s.replace "e.p." "").toList` |
| 10 | `dropEnd_ep_preserves_zero` | Parsing_SAN_Proofs.lean:44 | `s.endsWith "ep" → '0' ∈ s.toList → '0' ∈ (s.dropEnd 2).toString.toList` |
| 11 | `extractSanBase_ne_error` | Parsing_SAN_Proofs.lean:1750 | `'0' ∈ token.toList → extractSanBase token ≠ .error e` |
| 12 | `parseSanToken_succeeds_non_castle` | Parsing_SAN_Proofs.lean:1037 | `extractSanBase` succeeds on non-castle `moveToSAN` output |
| 13 | `parseSanToken_extracts_non_castle` | Parsing_SAN_Proofs.lean:1085 | `extractSanBase` recovers `moveToSanBase` from non-castle SAN |

### Dependency chain
- **9** depends on axiom 5 (`replace_eq_intercalate_splitOn`) + `splitOn`/`intercalate` membership
- **10** depends on axiom 3 (`dropRight_eq_legacy`) + character reasoning
- **11** depends on 9 + 10 + already-proved pipeline lemmas
- **12, 13** depend on axioms 4 (`trim`) + 5 (`replace`) being identity on chess notation chars, plus `endsWith` characterization

### What's already proved
- Castle cases of `parseSanToken_succeeds_on_moveToSAN` and `parseSanToken_extracts_moveToSanBase` via `native_decide`
- Character properties: `algebraic_chars_not_whitespace`, `algebraic_chars_not_dot`, `pieceLetter_chars`, `promotionSuffix_chars`
- Pipeline lemmas: `peelAnnotations_preserves_zero`, `dropWhile_plus_preserves_zero`, `trim_preserves_non_ws_char`

---

## Category 4: Chess-Structural — PROVABLE (2 axioms)

**Files:** KMinorMoveLemmas.lean, PerftProofs.lean
**Status:** Independent of String axioms. Provable with current infrastructure.

### Axiom 14: `mem_allLegalMoves_implies_not_king_destination`

| # | Name | File:Line | Statement |
|---|------|-----------|-----------|
| 14 | `mem_allLegalMoves_implies_not_king_destination` | KMinorMoveLemmas.lean:20 | No legal move targets a king |

**Approach:** Add `KingsPlusMinor` + `inCheck = false` preconditions. Proof uses:
- `KingsPlusMinor.kingSquare_white/black` to locate kings precisely
- Minor piece is not a king (`isMinorPiece`)
- If a king were captured, the attacker would put the opponent in check, contradicting `hNotInCheck`
- Agent D produced a working proof but it was reverted along with other changes. Can be re-applied.

### Axiom 15: `allLegalMoves_nodup`

| # | Name | File:Line | Statement |
|---|------|-----------|-----------|
| 15 | `allLegalMoves_nodup` | PerftProofs.lean:89 | `List.Nodup (allLegalMoves gs)` |

**What's needed:**
- Cross-square disjointness: moves from different squares have different `fromSq` — follows from `pieceTargets_sets_fromSq` (proved)
- Per-square uniqueness: each square generates moves with distinct `(toSq, promotion)` pairs
  - King standard / Knight: `filterMap` injectivity on `allSquares` (which is `Nodup` by `native_decide`)
  - Sliding pieces (Q/R/B): prove `walk` visits distinct squares per ray; different rays produce disjoint sets
  - Pawns: forward moves have distinct ranks, captures have distinct files, promotions differ by `promotion` field
- May need `hasValidKings gs.board` precondition to avoid duplicate castle moves

---

## Category 5: SAN Filter — INDEPENDENT (1 axiom)

**Files:** Parsing_SAN_Proofs.lean
**Status:** Requires SAN uniqueness integration with filter/singleton reasoning.

| # | Name | File:Line | Statement |
|---|------|-----------|-----------|
| 16 | `moveFromSanToken_finds_move` | Parsing_SAN_Proofs.lean:1587 | SAN filter over legal moves produces a move equivalent to `m` |

### What's needed
1. `m` is in the candidates list (from `moveToSanBase gs m = token.san`)
2. `sanDisambiguation` makes SAN strings unique among legal moves with the same piece type and target
3. `validateCheckHint` succeeds (check/mate hint is consistent)

SAN uniqueness is largely proved in `SanUniquenessFullProof.lean` but the integration with the filter/singleton argument is not yet done.

---

## Summary

| Category | Axioms | Status | Blocker |
|----------|--------|--------|---------|
| 1. String API bridges | 5 | BLOCKED | Lean 4.29 opaque `String.Internal.*` |
| 2. String-to-List bridges | 3 | BLOCKED | Category 1 |
| 3. SAN parsing pipeline | 5 | BLOCKED | Categories 1-2 |
| 4. Chess-structural | 2 | PROVABLE | Per-square uniqueness, king capture proof |
| 5. SAN filter | 1 | OPEN | SAN uniqueness integration |
| **Total** | **16** | | |

**Independently provable now:** Axioms 14-16 (Categories 4-5).
**Blocked on upstream:** Axioms 1-13 (Categories 1-3). All trace back to Lean 4.29's opaque String internals.
