import Chess.Analysis.AlphaBetaDepth2Proofs

namespace Chess
namespace Analysis

open Rules

/-!
Reusable “window correctness” statements for alpha-beta.

These are phrased in the classic fail-hard style:
- if the true minimax value is at least `β`, alpha-beta may return any value `≥ β` (fail-high)
- if the true minimax value is below `β` and the caller’s `α` is a valid lower bound,
  alpha-beta must return the exact minimax value (fail-low exactness)

This file currently contains fully proven base/slice results (depth 0 and depth 1),
and serves as the starting point for the depth-parametric induction roadmap in
`ALPHABETA_FULL_CORRECTNESS_PLAN.md`.
-/

def alphaBetaSound (depth : Nat) (gs : GameState) (α β : Int) : Prop :=
  β ≤ minimaxValue depth gs → β ≤ alphaBetaValue depth gs α β

def alphaBetaComplete (depth : Nat) (gs : GameState) (α β : Int) : Prop :=
  minimaxValue depth gs < β → α ≤ minimaxValue depth gs → alphaBetaValue depth gs α β = minimaxValue depth gs

theorem alphaBetaSound_depth0 (gs : GameState) (α β : Int) : alphaBetaSound 0 gs α β := by
  intro hβ
  -- Depth 0 alpha-beta is definitionally minimax.
  simpa [alphaBetaSound, alphaBetaValue_zero_eq_minimaxValue] using hβ

theorem alphaBetaComplete_depth0 (gs : GameState) (α β : Int) : alphaBetaComplete 0 gs α β := by
  intro _hLt _hα
  simp [alphaBetaComplete, alphaBetaValue_zero_eq_minimaxValue]

private def worst : Int :=
  -mateScore - 1

theorem alphaBetaSound_depth1_worst (gs : GameState) (β : Int) :
    alphaBetaSound 1 gs worst β := by
  intro hβ
  simpa [alphaBetaSound, worst] using
    (beta_le_alphaBetaValue_depth1_of_beta_le_minimaxValue (gs := gs) (β := β) hβ)

theorem alphaBetaComplete_depth1_worst (gs : GameState) (β : Int) :
    alphaBetaComplete 1 gs worst β := by
  intro hLt _hα
  -- The existing lemma already gives exactness from the strict `< β` hypothesis at depth 1.
  simpa [alphaBetaComplete, worst] using
    (alphaBetaValue_depth1_eq_minimaxValue_of_minimax_lt_beta (gs := gs) (β := β) hLt)
end Analysis
end Chess
