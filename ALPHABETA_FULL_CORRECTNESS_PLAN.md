# Alpha-Beta Full Correctness Plan (Proof Roadmap)

Goal: prove the optimization layer is semantics-preserving.

## Target Theorem (end state)

For all game states and depths:
- `Chess/Analysis/AlphaBeta.lean`: `alphaBeta depth gs = minimaxValue depth gs`

Equivalently (since `negamax_eq_minimaxValue` is already proven):
- `alphaBeta depth gs = negamax depth gs`

## Current Status (already in repo)

- Spec: `Chess/Analysis/MinimaxSpec.lean` (`minimaxValue`)
- Baseline equivalence: `Chess/Analysis/Equivalence.lean` (`negamax_eq_minimaxValue`)
- Alpha-beta implementation: `Chess/Analysis/AlphaBeta.lean`
- Slices:
  - Depth 1: `Chess/Analysis/AlphaBetaDepth1Proofs.lean` (`alphaBeta_depth1_eq_minimaxValue`)
  - Depth 2: `Chess/Analysis/AlphaBetaDepth2Proofs.lean` (`alphaBeta_depth2_eq_minimaxValue`)
- Bounds to support pruning arguments:
  - `Chess/Analysis/MinimaxBounds.lean` (`minimaxValue_bounds`)

## Why This Is Hard

Our alpha-beta is fail-hard negamax:
- returns an exact value if it finishes “below beta”
- may return a cutoff value `≥ β` (not necessarily equal to the true minimax) when pruning

So we prove a *windowed correctness* invariant, then specialize it to the root window
`[-mateScore-1, mateScore+1]` where pruning cannot change the final value.

## Proposed Proof Structure (incremental, non-crossed)

### 1) Prove generic window soundness/completeness (depth-parametric)

Define the “window correctness” predicates (names are suggestions):

- **Soundness (lower bound):**
  - If `β ≤ minimaxValue d gs` then `β ≤ alphaBetaValue d gs α β`
  - Intuition: when the true value is at least beta, alpha-beta is allowed to return a fail-high.

- **Completeness (exactness under fail-low):**
  - If `minimaxValue d gs < β` and `α ≤ minimaxValue d gs` then
    `alphaBetaValue d gs α β = minimaxValue d gs`
  - Intuition: when the true value is strictly below beta, pruning is impossible and the search is exact.

These are the classic two lemmas that make alpha-beta correctness compositional.

### 2) Establish helper invariants for the list scan

Prove the “single-step” facts needed to carry the depth induction through the `alphaBetaList` loop:

- `alphaBetaList` accumulator is monotone: never decreases `α`
- When `α' ≥ β`, the returned value is `≥ β` (cutoff is a valid fail-high)
- If the final result is `< β`, then no cutoff occurred (so the list scan equals the corresponding fold)

### 3) Induct on depth

Inductive hypothesis provides window correctness at depth `d` for all children.
Use it to show window correctness at depth `d+1` by analyzing one `alphaBetaList` step:

- If a child’s true score would raise alpha, show the recursive call returns the exact child minimax.
- If it would not raise alpha, show the recursive call cannot produce a score that incorrectly raises alpha
  (it may still fail-high, but that’s safe because it implies the child’s true value is already `≥ βChild`).

### 4) Specialize to the exported API

Use `minimaxValue_bounds`:
- `minimaxValue d gs ≤ mateScore`, hence `minimaxValue d gs < mateScore + 1`

Therefore `alphaBeta d gs = alphaBetaValue d gs (-mateScore-1) (mateScore+1)` is exact:
- `alphaBeta d gs = minimaxValue d gs`

## Suggested Milestones (before the final theorem)

- Depth 3 slice: `alphaBeta 3 gs = minimaxValue 3 gs` (validates the induction plumbing one level deeper)
- Window correctness for depth 1 with arbitrary `(α,β)` (needed for deeper slices/induction)
- Window correctness for depth 2 with arbitrary `(α,β)` (first genuinely pruning-sensitive level)

## Where To Put Things

- Window invariants: `Chess/Analysis/AlphaBetaWindow.lean` (new)
- List-scan lemmas: `Chess/Analysis/AlphaBetaListLemmas.lean` (new, optional)
- Full theorem: `Chess/Analysis/AlphaBetaCorrectness.lean` (new)
- Update `THEOREM_INDEX.md` when each milestone lands.

