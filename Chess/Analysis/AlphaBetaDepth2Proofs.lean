import Chess.Analysis.AlphaBetaDepth1Proofs
import Chess.Analysis.MinimaxBounds

namespace Chess
namespace Analysis

open Rules

private def worst : Int :=
  -mateScore - 1

private def depth0Score (gs : GameState) (m : Move) : Int :=
  by
    let child := GameState.playMove gs m
    exact
      -(match terminalValue? child with
        | some v => v
        | none => staticEval child)

private def depth1TrueScore (gs : GameState) (m : Move) : Int :=
  -(minimaxValue 1 (GameState.playMove gs m))

private def maxStep (gs : GameState) (best : Int) (m : Move) : Int :=
  let score := depth0Score gs m
  if best < score then score else best

private theorem minimaxValue_one_eq_foldl_maxStep (gs : GameState)
    (hTerm : terminalValue? gs = none) :
    minimaxValue 1 gs = (allLegalMoves gs).foldl (maxStep gs) worst := by
  -- Unfold the depth-1 minimax and normalize the depth-0 score shape.
  simp [minimaxValue, hTerm, worst]
  -- The remaining fold steps are definitionally equal after unfolding `maxStep`/`depth0Score`.
  unfold maxStep depth0Score
  simp [minimaxValue]
  rfl

private theorem le_foldl_maxStep (gs : GameState) (ms : List Move) (a : Int) :
    a ≤ ms.foldl (maxStep gs) a := by
  induction ms generalizing a with
  | nil =>
      simp [List.foldl]
  | cons m ms ih =>
      -- One step of the fold updates to `maxStep gs a m`, then never decreases.
      have hInit : a ≤ maxStep gs a m := by
        unfold maxStep
        by_cases hBetter : a < depth0Score gs m
        · simpa [hBetter] using (Int.le_of_lt hBetter)
        · simp [hBetter]
      simpa [List.foldl] using Int.le_trans hInit (ih (a := maxStep gs a m))

theorem alphaBetaList_depth0_eq_foldl_of_fold_lt_beta
    (gs : GameState) (ms : List Move) (α β : Int)
    (hFold : ms.foldl (maxStep gs) α < β) :
    alphaBetaValue.alphaBetaList 0 gs ms α β = ms.foldl (maxStep gs) α := by
  induction ms generalizing α with
  | nil =>
      simp [alphaBetaValue.alphaBetaList]
  | cons m ms ih =>
      let child := GameState.playMove gs m
      have hScoreEq :
          (-(alphaBetaValue 0 child (-β) (-α))) = depth0Score gs m := by
        have h0 := alphaBetaValue_zero_eq_minimaxValue child (-β) (-α)
        simpa [depth0Score, minimaxValue, child] using congrArg (fun x => -x) h0
      let score := depth0Score gs m
      let α' := if score > α then score else α
      have hTail : ms.foldl (maxStep gs) α' < β := by
        simpa [List.foldl, maxStep, score, α'] using hFold
      have hα'Lt : α' < β := by
        have hLe : α' ≤ ms.foldl (maxStep gs) α' := le_foldl_maxStep gs ms α'
        exact Int.lt_of_le_of_lt hLe hTail
      have hNoPrune : ¬ α' ≥ β := by
        exact Int.not_le_of_gt hα'Lt
      have hRec :
          alphaBetaValue.alphaBetaList 0 gs (m :: ms) α β =
            alphaBetaValue.alphaBetaList 0 gs ms α' β := by
        simp [alphaBetaValue.alphaBetaList, child, score, α', hScoreEq, hNoPrune]
      calc
        alphaBetaValue.alphaBetaList 0 gs (m :: ms) α β
            = alphaBetaValue.alphaBetaList 0 gs ms α' β := hRec
        _ = ms.foldl (maxStep gs) α' := ih (α := α') hTail
        _ = (m :: ms).foldl (maxStep gs) α := by
            simp [List.foldl, maxStep, score, α']

theorem alphaBetaValue_depth1_eq_minimaxValue_of_minimax_lt_beta
    (gs : GameState) (β : Int) (hβ : minimaxValue 1 gs < β) :
    alphaBetaValue 1 gs worst β = minimaxValue 1 gs := by
  cases hTerm : terminalValue? gs with
  | some v =>
      simp [alphaBetaValue, minimaxValue, hTerm]
  | none =>
      -- Reduce to the shared `foldl`, then use that the fold result is < β (so no prune happens).
      have hFold : (allLegalMoves gs).foldl (maxStep gs) worst < β := by
        have hEq := minimaxValue_one_eq_foldl_maxStep (gs := gs) hTerm
        simpa [hEq] using hβ
      have hAB :
          alphaBetaValue 1 gs worst β =
            (allLegalMoves gs).foldl (maxStep gs) worst := by
        simp [alphaBetaValue, hTerm, worst]
        simpa using
          (alphaBetaList_depth0_eq_foldl_of_fold_lt_beta (gs := gs) (ms := allLegalMoves gs) (α := worst) (β := β) hFold)
      have hMin : (allLegalMoves gs).foldl (maxStep gs) worst = minimaxValue 1 gs := by
        simpa using (minimaxValue_one_eq_foldl_maxStep (gs := gs) hTerm).symm
      exact Eq.trans hAB hMin

theorem alphaBetaValue_depth1_eq_minimaxValue_of_result_lt_beta
    (gs : GameState) (β : Int) (hRes : alphaBetaValue 1 gs worst β < β) :
    alphaBetaValue 1 gs worst β = minimaxValue 1 gs := by
  cases hTerm : terminalValue? gs with
  | some v =>
      simp [alphaBetaValue, minimaxValue, hTerm]
  | none =>
      -- If the final value is < β, then no prune occurred; the list scan matches the full fold.
      have hList :
          alphaBetaValue.alphaBetaList 0 gs (allLegalMoves gs) worst β =
            (allLegalMoves gs).foldl (maxStep gs) worst := by
        -- Prove the accumulator-parametric statement, then instantiate at `worst`.
        generalize hMoves : allLegalMoves gs = ms
        have hAux :
            ∀ (ms : List Move) (α0 : Int),
              alphaBetaValue.alphaBetaList 0 gs ms α0 β < β →
                alphaBetaValue.alphaBetaList 0 gs ms α0 β = ms.foldl (maxStep gs) α0 := by
          intro ms
          induction ms with
          | nil =>
              intro α0 hRes
              simp [alphaBetaValue.alphaBetaList, List.foldl] at hRes ⊢
          | cons m ms ih =>
              intro α0 hRes
              let child := GameState.playMove gs m
              have hScoreEq :
                  (-(alphaBetaValue 0 child (-β) (-α0))) = depth0Score gs m := by
                have h0 := alphaBetaValue_zero_eq_minimaxValue child (-β) (-α0)
                simpa [depth0Score, minimaxValue, child] using congrArg (fun x => -x) h0
              let score := depth0Score gs m
              let α' := if score > α0 then score else α0
              have hNoPrune : ¬ α' ≥ β := by
                intro hPrune
                have hEq :
                    alphaBetaValue.alphaBetaList 0 gs (m :: ms) α0 β = α' := by
                  simp [alphaBetaValue.alphaBetaList, child, score, α', hScoreEq, hPrune]
                have hLt : α' < β := by
                  simpa [hEq] using hRes
                exact (Int.not_le_of_gt hLt) hPrune
              have hEqRec :
                  alphaBetaValue.alphaBetaList 0 gs (m :: ms) α0 β =
                    alphaBetaValue.alphaBetaList 0 gs ms α' β := by
                simp [alphaBetaValue.alphaBetaList, child, score, α', hScoreEq, hNoPrune]
              have hResTail : alphaBetaValue.alphaBetaList 0 gs ms α' β < β := by
                simpa [hEqRec] using hRes
              have ih' := ih (α0 := α') hResTail
              simpa [List.foldl, maxStep, score, α', hEqRec] using ih'
        have h' :=
          hAux ms worst (by
            -- Expand `alphaBetaValue 1` to the underlying `alphaBetaList 0` since we're non-terminal.
            simpa [alphaBetaValue, hTerm, hMoves, worst] using hRes)
        simpa [hMoves] using h'
      have hAB :
          alphaBetaValue 1 gs worst β = (allLegalMoves gs).foldl (maxStep gs) worst := by
        simpa [alphaBetaValue, hTerm, worst] using hList
      have hMin : (allLegalMoves gs).foldl (maxStep gs) worst = minimaxValue 1 gs := by
        simpa using (minimaxValue_one_eq_foldl_maxStep (gs := gs) hTerm).symm
      exact Eq.trans hAB hMin

theorem beta_le_alphaBetaValue_depth1_of_beta_le_minimaxValue
    (gs : GameState) (β : Int) (hβ : β ≤ minimaxValue 1 gs) :
    β ≤ alphaBetaValue 1 gs worst β := by
  by_cases hOk : β ≤ alphaBetaValue 1 gs worst β
  · exact hOk
  ·
    have hLt : alphaBetaValue 1 gs worst β < β := Int.lt_of_not_ge hOk
    have hEq :=
      alphaBetaValue_depth1_eq_minimaxValue_of_result_lt_beta (gs := gs) (β := β) hLt
    have : minimaxValue 1 gs < β := by
      simpa [hEq] using hLt
    exact False.elim ((Int.not_lt_of_ge hβ) this)

theorem alphaBetaList_depth1_eq_foldl_trueScore
    (gs : GameState) (ms : List Move) (α : Int)
    (hα : α ≤ mateScore) :
    alphaBetaValue.alphaBetaList 1 gs ms α (mateScore + 1) =
      ms.foldl
        (fun best m =>
          let score := depth1TrueScore gs m
          if score > best then score else best)
        α := by
  induction ms generalizing α with
  | nil =>
      simp [alphaBetaValue.alphaBetaList]
  | cons m ms ih =>
      have hNegBeta : (-(mateScore + 1) : Int) = -mateScore - 1 := by
        native_decide
      let child := GameState.playMove gs m
      let scoreTrue := depth1TrueScore gs m
      have hScoreBounds :
          -mateScore ≤ scoreTrue ∧ scoreTrue ≤ mateScore := by
        have hb := minimaxValue_bounds 1 child
        constructor
        · -- from `child ≤ mateScore`
          have : -mateScore ≤ -(minimaxValue 1 child) := by
            simpa using (Int.neg_le_neg hb.2)
          simpa [depth1TrueScore, scoreTrue, child] using this
        · -- from `-mateScore ≤ child`
          have : -(minimaxValue 1 child) ≤ mateScore := by
            simpa using (Int.neg_le_neg hb.1)
          simpa [depth1TrueScore, scoreTrue, child] using this
      let βChild : Int := -α
      let scoreAB : Int := -(alphaBetaValue 1 child (-(mateScore + 1)) (-α))
      have hScoreAB :
          (scoreTrue > α → scoreAB = scoreTrue) ∧ (¬ scoreTrue > α → scoreAB ≤ α) := by
        constructor
        · intro hBetter
          have hChildLt : minimaxValue 1 child < βChild := by
            -- `-(minimaxValue 1 child) > α` -> `minimaxValue 1 child < -α`.
            have : -(minimaxValue 1 child) > α := by
              simpa [depth1TrueScore, scoreTrue, child] using hBetter
            have hlt : α < -(minimaxValue 1 child) := by
              simpa using this
            have : minimaxValue 1 child < -α := by
              simpa using (Int.neg_lt_neg hlt)
            simpa [βChild] using this
          have hEqChild :=
            alphaBetaValue_depth1_eq_minimaxValue_of_minimax_lt_beta (gs := child) (β := βChild) hChildLt
          have hEqChild' : alphaBetaValue 1 child (-(mateScore + 1)) βChild = minimaxValue 1 child := by
            -- `-(mateScore+1)` is definitionaly the same lower bound as `worst`.
            simpa [worst, hNegBeta] using hEqChild
          simp [scoreAB, scoreTrue, depth1TrueScore, βChild, child, hEqChild']
        · intro hNotBetter
          have hChildLe : βChild ≤ minimaxValue 1 child := by
            -- `¬ (-(minimaxValue 1 child) > α)` means `-(minimaxValue 1 child) ≤ α`, so `-α ≤ minimaxValue`.
            have hLe : -(minimaxValue 1 child) ≤ α := by
              -- `¬ (α < scoreTrue)` gives `scoreTrue ≤ α`.
              have : scoreTrue ≤ α := by
                by_cases hLe' : scoreTrue ≤ α
                · exact hLe'
                ·
                  have hlt : α < scoreTrue := Int.lt_of_not_ge hLe'
                  cases hNotBetter (by simpa using hlt)
              simpa [depth1TrueScore, scoreTrue, child] using this
            -- Negate both sides.
            simpa [βChild] using (Int.neg_le_neg hLe)
          have hBetaLe : βChild ≤ alphaBetaValue 1 child (-(mateScore + 1)) βChild := by
            have hTmp : βChild ≤ alphaBetaValue 1 child worst βChild :=
              beta_le_alphaBetaValue_depth1_of_beta_le_minimaxValue (gs := child) (β := βChild) hChildLe
            simpa [worst, hNegBeta] using hTmp
          have : scoreAB ≤ α := by
            -- `βChild ≤ childValue` -> `-childValue ≤ -βChild = α`
            have : -(alphaBetaValue 1 child (-(mateScore + 1)) βChild) ≤ -βChild :=
              Int.neg_le_neg hBetaLe
            simpa [scoreAB, βChild] using this
          exact this
      let αTrue' : Int := if scoreTrue > α then scoreTrue else α
      let αAB' : Int := if scoreAB > α then scoreAB else α
      have hUpdate : αAB' = αTrue' := by
        by_cases hBetter : scoreTrue > α
        ·
          have hEq : scoreAB = scoreTrue := (hScoreAB.1 hBetter)
          have hBetter' : scoreAB > α := by simpa [hEq] using hBetter
          simp [αAB', αTrue', hBetter, hBetter', hEq]
        ·
          have hLe : scoreAB ≤ α := hScoreAB.2 hBetter
          have hBetter' : ¬ scoreAB > α := by
            intro hGt
            exact (Int.not_le_of_gt hGt) hLe
          simp [αAB', αTrue', hBetter, hBetter']
      have hαTrueLe : αTrue' ≤ mateScore := by
        by_cases hBetter : scoreTrue > α
        ·
          have : scoreTrue ≤ mateScore := hScoreBounds.2
          simp [αTrue', hBetter, this]
        ·
          simp [αTrue', hBetter, hα]
      have hMateLt : mateScore < mateScore + 1 := by
        native_decide
      have hNoPrune : ¬ αAB' ≥ mateScore + 1 := by
        have hLt : αAB' < mateScore + 1 := by
          have : αAB' ≤ mateScore := by simpa [hUpdate] using hαTrueLe
          exact Int.lt_of_le_of_lt this hMateLt
        exact Int.not_le_of_gt hLt
      have hRec :
          alphaBetaValue.alphaBetaList 1 gs (m :: ms) α (mateScore + 1) =
            alphaBetaValue.alphaBetaList 1 gs ms αAB' (mateScore + 1) := by
        simp [alphaBetaValue.alphaBetaList, child, scoreAB, αAB', hNoPrune]
      calc
        alphaBetaValue.alphaBetaList 1 gs (m :: ms) α (mateScore + 1)
            = alphaBetaValue.alphaBetaList 1 gs ms αAB' (mateScore + 1) := hRec
        _ =
            ms.foldl
              (fun best m =>
                let score := depth1TrueScore gs m
                if score > best then score else best)
              αAB' := ih (α := αAB') (by
                -- `αAB' ≤ mateScore` via the `true` update bound.
                have : αAB' ≤ mateScore := by simpa [hUpdate] using hαTrueLe
                exact this)
        _ =
            (m :: ms).foldl
              (fun best m =>
                let score := depth1TrueScore gs m
                if score > best then score else best)
              α := by
            simp [List.foldl, αTrue', hUpdate, depth1TrueScore, scoreTrue]

theorem alphaBeta_depth2_eq_minimaxValue (gs : GameState) :
    alphaBeta 2 gs = minimaxValue 2 gs := by
  unfold alphaBeta
  cases hTerm : terminalValue? gs with
  | some v =>
      simp [alphaBetaValue, minimaxValue, hTerm]
  | none =>
      have hWorst : (worst : Int) ≤ mateScore := by
        native_decide
      have hAB :
          alphaBetaValue 2 gs worst (mateScore + 1) =
            (allLegalMoves gs).foldl
              (fun best m =>
                let score := depth1TrueScore gs m
                if score > best then score else best)
              worst := by
        simp [alphaBetaValue, hTerm, worst]
        simpa using
          (alphaBetaList_depth1_eq_foldl_trueScore (gs := gs) (ms := allLegalMoves gs) (α := worst) hWorst)
      have hMin :
          minimaxValue 2 gs =
            (allLegalMoves gs).foldl
              (fun best m =>
                let score := depth1TrueScore gs m
                if score > best then score else best)
              worst := by
        simp [minimaxValue, hTerm, worst, depth1TrueScore]
      exact Eq.trans hAB hMin.symm

theorem alphaBeta_depth2_eq_negamax (gs : GameState) :
    alphaBeta 2 gs = negamax 2 gs := by
  simp [alphaBeta_depth2_eq_minimaxValue, negamax_eq_minimaxValue]

end Analysis
end Chess
