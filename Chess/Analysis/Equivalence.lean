import Chess.Analysis.Baseline
import Chess.Analysis.MinimaxSpec

namespace Chess
namespace Analysis

open Rules

theorem negamaxPV_value_eq_minimaxValue (depth : Nat) (gs : GameState) :
    (negamaxPV depth gs).value = minimaxValue depth gs := by
  induction depth generalizing gs with
  | zero =>
      cases hTerm : terminalValue? gs with
      | some v =>
          simp [negamaxPV, minimaxValue, hTerm]
      | none =>
          simp [negamaxPV, minimaxValue, hTerm]
  | succ d ih =>
      cases hTerm : terminalValue? gs with
      | some v =>
          simp [negamaxPV, minimaxValue, hTerm]
      | none =>
          -- Reduce both sides to related `foldl`s over the same `moves` list.
          generalize hMoves : allLegalMoves gs = moves
          let worstPV : PVResult := { value := -mateScore - 1, pv := [] }
          let worstI : Int := -mateScore - 1
          let stepPV : PVResult → Move → PVResult :=
            fun best m =>
              let child := GameState.playMove gs m
              let childRes := negamaxPV d child
              let scorePV : Int := -childRes.value
              if scorePV > best.value then
                { value := scorePV, pv := m :: childRes.pv }
              else
                best
          let stepI : Int → Move → Int :=
            fun best m =>
              let child := GameState.playMove gs m
              let scoreI : Int := -(minimaxValue d child)
              if scoreI > best then scoreI else best
          have hFold :
              ∀ (ms : List Move) (best : PVResult) (bestI : Int),
                best.value = bestI →
                  ((ms.foldl stepPV best).value) = (ms.foldl stepI bestI) := by
            intro ms
            induction ms with
            | nil =>
                intro best bestI hEq
                simpa [List.foldl] using hEq
            | cons m ms ihMs =>
                intro best bestI hEq
                let child := GameState.playMove gs m
                have hScore :
                    (-(negamaxPV d child).value) = (-(minimaxValue d child)) := by
                  have hChild := ih (gs := child)
                  simpa using congrArg (fun x => -x) hChild
                let scorePV : Int := -(negamaxPV d child).value
                let scoreI : Int := -(minimaxValue d child)
                have hScore' : scorePV = scoreI := by
                  simpa [scorePV, scoreI] using hScore
                by_cases hBetter : scorePV > best.value
                ·
                  have hBetterI : scoreI > bestI := by
                    simpa [hScore', hEq] using hBetter
                  have hNextRel : (stepPV best m).value = stepI bestI m := by
                    simp [stepPV, stepI, child, scorePV, scoreI, hBetterI, hScore', hEq]
                  simpa [List.foldl] using
                    (ihMs (best := stepPV best m) (bestI := stepI bestI m) hNextRel)
                ·
                  have hBetterI : ¬ scoreI > bestI := by
                    simpa [hScore', hEq] using hBetter
                  have hNextRel : (stepPV best m).value = stepI bestI m := by
                    simp [stepPV, stepI, child, scorePV, scoreI, hBetterI, hScore', hEq]
                  simpa [List.foldl] using
                    (ihMs (best := stepPV best m) (bestI := stepI bestI m) hNextRel)
          have hWorst : worstPV.value = worstI := by
            rfl
          -- Finish by unfolding both definitions and applying `hFold`.
          simpa [negamaxPV, minimaxValue, hTerm, hMoves, worstPV, worstI, stepPV, stepI] using
            (hFold moves worstPV worstI hWorst)

theorem negamax_eq_minimaxValue (depth : Nat) (gs : GameState) :
    negamax depth gs = minimaxValue depth gs := by
  simp [negamax, negamaxPV_value_eq_minimaxValue]

end Analysis
end Chess
