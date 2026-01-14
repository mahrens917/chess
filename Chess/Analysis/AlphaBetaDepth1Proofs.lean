import Chess.Analysis.AlphaBeta
import Chess.Analysis.Bounds
import Chess.Analysis.Equivalence

namespace Chess
namespace Analysis

open Rules

theorem alphaBetaValue_zero_eq_minimaxValue (gs : GameState) (α β : Int) :
    alphaBetaValue 0 gs α β = minimaxValue 0 gs := by
  cases hTerm : terminalValue? gs with
  | some v =>
      simp [alphaBetaValue, minimaxValue, hTerm]
  | none =>
      simp [alphaBetaValue, minimaxValue, hTerm]

private def depth0Score (gs : GameState) (m : Move) : Int :=
  -(minimaxValue 0 (GameState.playMove gs m))

private theorem depth0Score_le_mateScore (gs : GameState) (m : Move) :
    depth0Score gs m ≤ mateScore := by
  -- `-(minimaxValue 0 child) ≤ mateScore` follows from `-mateScore ≤ minimaxValue 0 child`.
  have hBounds := minimaxValue_zero_bounds (GameState.playMove gs m)
  have hLower : -mateScore ≤ minimaxValue 0 (GameState.playMove gs m) := hBounds.1
  -- Negate both sides: `-(minimaxValue ..) ≤ mateScore`.
  have : -(minimaxValue 0 (GameState.playMove gs m)) ≤ mateScore := by
    simpa using (Int.neg_le_neg hLower)
  simpa [depth0Score] using this

theorem alphaBetaList_depth0_eq_foldl
    (gs : GameState) (ms : List Move) (α : Int)
    (hα : α ≤ mateScore) :
    alphaBetaValue.alphaBetaList 0 gs ms α (mateScore + 1) =
      ms.foldl
        (fun best m =>
          let score := depth0Score gs m
          if score > best then score else best)
        α := by
  induction ms generalizing α with
  | nil =>
      simp [alphaBetaValue.alphaBetaList]
  | cons m ms ih =>
      -- Unfold one alpha-beta list step.
      let child := GameState.playMove gs m
      let score := depth0Score gs m
      let α' := if score > α then score else α
      have hScoreLe : score ≤ mateScore := by
        simpa [score] using depth0Score_le_mateScore gs m
      have hAlphaLe : α' ≤ mateScore := by
        by_cases hBetter : score > α
        ·
          simp [α', hBetter]
          exact hScoreLe
        ·
          simp [α', hBetter]
          exact hα
      have hMateLt : mateScore < mateScore + 1 := by
        native_decide
      have hAlphaLt : α' < mateScore + 1 := Int.lt_of_le_of_lt hAlphaLe hMateLt
      have hNoPrune : ¬ α' ≥ mateScore + 1 := by
        -- `α' ≥ β` is `β ≤ α'`; contradiction from `α' < β`.
        exact Int.not_le_of_gt hAlphaLt
      -- Rewrite the recursive definition, using that the prune branch is impossible.
      have hRec :
          alphaBetaValue.alphaBetaList 0 gs (m :: ms) α (mateScore + 1) =
            alphaBetaValue.alphaBetaList 0 gs ms α' (mateScore + 1) := by
        -- Identify the algorithm's score with our `depth0Score`.
        have hScoreEq :
            (-(alphaBetaValue 0 child (-(mateScore + 1)) (-α))) = score := by
          -- alphaBetaValue at depth 0 ignores bounds.
          have h0 := alphaBetaValue_zero_eq_minimaxValue child (-(mateScore + 1)) (-α)
          simpa [score, depth0Score, child] using congrArg (fun x => -x) h0
        -- Rewrite the step using the above equality and simplify the (impossible) prune.
        simp [alphaBetaValue.alphaBetaList, child, score, α', hScoreEq, hNoPrune]
      -- Foldl evolves the accumulator in the same way.
      have hFold :
          (List.foldl
              (fun best m =>
                let score := depth0Score gs m
                if score > best then score else best)
              α
              (m :: ms)) =
            List.foldl
              (fun best m =>
                let score := depth0Score gs m
                if score > best then score else best)
              α'
              ms := by
        by_cases hBetter : score > α
        · simp [List.foldl, α', hBetter, score]
        · simp [List.foldl, α', hBetter, score]
      -- Combine.
      calc
        alphaBetaValue.alphaBetaList 0 gs (m :: ms) α (mateScore + 1)
            = alphaBetaValue.alphaBetaList 0 gs ms α' (mateScore + 1) := hRec
        _ = List.foldl
              (fun best m =>
                let score := depth0Score gs m
                if score > best then score else best)
              α'
              ms := ih (α := α') hAlphaLe
        _ = List.foldl
              (fun best m =>
                let score := depth0Score gs m
                if score > best then score else best)
              α
              (m :: ms) := by
            simp [hFold]

theorem alphaBeta_depth1_eq_minimaxValue (gs : GameState) :
    alphaBeta 1 gs = minimaxValue 1 gs := by
  unfold alphaBeta
  cases hTerm : terminalValue? gs with
  | some v =>
      simp [alphaBetaValue, minimaxValue, hTerm]
  | none =>
      -- Unfold both sides and reduce to the shared foldl.
      have hWorst : (-mateScore - 1 : Int) ≤ mateScore := by
        native_decide
      -- alphaBetaValue at depth 1 uses `alphaBetaList 0`.
      have hAB :
          alphaBetaValue 1 gs (-mateScore - 1) (mateScore + 1) =
            (allLegalMoves gs).foldl
              (fun best m =>
                let score := depth0Score gs m
                if score > best then score else best)
              (-mateScore - 1) := by
        simp [alphaBetaValue, hTerm, alphaBetaValue_zero_eq_minimaxValue, depth0Score]
        -- Discharge the alphaBetaList fold conversion.
        simpa using
          (alphaBetaList_depth0_eq_foldl (gs := gs) (ms := allLegalMoves gs) (α := (-mateScore - 1)) hWorst)
      -- minimaxValue at depth 1 is the same fold, by definition.
      simp [minimaxValue, hTerm, hAB, depth0Score]

theorem alphaBeta_depth1_eq_negamax (gs : GameState) :
    alphaBeta 1 gs = negamax 1 gs := by
  -- Baseline `negamax` is already proven equal to `minimaxValue`.
  simp [alphaBeta_depth1_eq_minimaxValue, negamax_eq_minimaxValue]

end Analysis
end Chess
