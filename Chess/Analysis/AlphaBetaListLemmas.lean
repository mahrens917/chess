import Chess.Analysis.AlphaBeta

namespace Chess
namespace Analysis

open Rules

/-!
Small reusable facts about the `alphaBetaList` loop.

These are intended as building blocks for the full-depth correctness proof
roadmap in `ALPHABETA_FULL_CORRECTNESS_PLAN.md`.
-/

def alphaBetaListNoCutoff (d : Nat) (gs : GameState) : List Move → Int → Int → Int
  | [], α, _β => α
  | m :: ms, α, β =>
      let child := GameState.playMove gs m
      let score := -(alphaBetaValue d child (-β) (-α))
      let α' := if score > α then score else α
      alphaBetaListNoCutoff d gs ms α' β

theorem alphaBetaList_ge_alpha (d : Nat) (gs : GameState) (ms : List Move) (α β : Int) :
    α ≤ alphaBetaValue.alphaBetaList d gs ms α β := by
  induction ms generalizing α with
  | nil =>
      simp [alphaBetaValue.alphaBetaList]
  | cons m ms ih =>
      let child := GameState.playMove gs m
      let score := -(alphaBetaValue d child (-β) (-α))
      let α' := if score > α then score else α
      have hAlphaLe : α ≤ α' := by
        by_cases hBetter : score > α
        ·
          have : α < score := hBetter
          have : α ≤ score := Int.le_of_lt this
          simpa [α', hBetter] using this
        ·
          simp [α', hBetter]
      by_cases hPrune : α' ≥ β
      · -- Cutoff returns `α'`.
        simpa [alphaBetaValue.alphaBetaList, child, score, α', hPrune] using hAlphaLe
      · -- No cutoff: recurse with `α'` and use IH + transitivity.
        have hRec : α' ≤ alphaBetaValue.alphaBetaList d gs ms α' β := ih (α := α')
        have : α ≤ alphaBetaValue.alphaBetaList d gs ms α' β :=
          Int.le_trans hAlphaLe hRec
        simpa [alphaBetaValue.alphaBetaList, child, score, α', hPrune] using this

/--
If `alphaBetaList` returns a value strictly below `β`, then the cutoff branch did not trigger
on the head element, and the result comes from the recursive tail call.
-/
theorem alphaBetaList_lt_beta_cons
    (d : Nat) (gs : GameState) (m : Move) (ms : List Move) (α β : Int)
    (h : alphaBetaValue.alphaBetaList d gs (m :: ms) α β < β) :
    let child := GameState.playMove gs m
    let score := -(alphaBetaValue d child (-β) (-α))
    let α' := if score > α then score else α
    (¬ α' ≥ β) ∧
      alphaBetaValue.alphaBetaList d gs (m :: ms) α β =
        alphaBetaValue.alphaBetaList d gs ms α' β ∧
      alphaBetaValue.alphaBetaList d gs ms α' β < β := by
  intro child score α'
  by_cases hPrune : α' ≥ β
  ·
    -- Contradiction: cutoff would return `α' ≥ β`.
    have hEq : alphaBetaValue.alphaBetaList d gs (m :: ms) α β = α' := by
      simp [alphaBetaValue.alphaBetaList, child, score, α', hPrune]
    have : α' < β := by
      simpa [hEq] using h
    cases (Int.not_lt_of_ge hPrune) this
  ·
    have hEq :
        alphaBetaValue.alphaBetaList d gs (m :: ms) α β =
          alphaBetaValue.alphaBetaList d gs ms α' β := by
      simp [alphaBetaValue.alphaBetaList, child, score, α', hPrune]
    refine ⟨hPrune, ?_, ?_⟩
    · exact hEq
    · simpa [hEq] using h

theorem alphaBetaList_lt_beta_implies_eq_noCutoff
    (d : Nat) (gs : GameState) (ms : List Move) (α β : Int)
    (h : alphaBetaValue.alphaBetaList d gs ms α β < β) :
    alphaBetaValue.alphaBetaList d gs ms α β = alphaBetaListNoCutoff d gs ms α β := by
  induction ms generalizing α with
  | nil =>
      simp [alphaBetaValue.alphaBetaList, alphaBetaListNoCutoff] at h ⊢
  | cons m ms ih =>
      have hStep :=
        alphaBetaList_lt_beta_cons (d := d) (gs := gs) (m := m) (ms := ms) (α := α) (β := β) h
      -- Unpack the head step.
      rcases hStep with ⟨_hNoCut, hEqRec, hTailLt⟩
      -- Compute the same `α'` as the definition, and apply IH to the tail.
      let child := GameState.playMove gs m
      let score := -(alphaBetaValue d child (-β) (-α))
      let α' := if score > α then score else α
      have hEqRec' :
          alphaBetaValue.alphaBetaList d gs (m :: ms) α β =
            alphaBetaValue.alphaBetaList d gs ms α' β := by
        simpa [child, score, α'] using hEqRec
      have hTailEq : alphaBetaValue.alphaBetaList d gs ms α' β = alphaBetaListNoCutoff d gs ms α' β :=
        ih (α := α') hTailLt
      calc
        alphaBetaValue.alphaBetaList d gs (m :: ms) α β
            = alphaBetaValue.alphaBetaList d gs ms α' β := hEqRec'
        _ = alphaBetaListNoCutoff d gs ms α' β := hTailEq
        _ = alphaBetaListNoCutoff d gs (m :: ms) α β := by
            simp [alphaBetaListNoCutoff, child, score, α']

end Analysis
end Chess
