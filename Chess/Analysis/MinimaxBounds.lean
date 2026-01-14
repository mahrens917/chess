import Chess.Analysis.MinimaxSpec
import Chess.Analysis.Bounds

namespace Chess
namespace Analysis

open Rules

theorem terminalValue?_none_implies_noLegalMoves_false (gs : GameState) :
    terminalValue? gs = none → Rules.noLegalMoves gs = false := by
  intro hNone
  -- If `noLegalMoves = true`, the position is either checkmate or stalemate (or already a result),
  -- so `terminalValue?` cannot be `none`.
  by_cases hNo : Rules.noLegalMoves gs = true
  ·
    have hContra : False := by
      -- Split on check status: checkmate vs stalemate/result.
      cases hIn : Rules.inCheckStatus gs with
      | true =>
          have hMate : isCheckmate gs = true := by
            unfold Rules.isCheckmate
            simp [hIn, hNo]
          have hSome : terminalValue? gs = some (-mateScore) := by
            unfold terminalValue?
            simp [hMate]
          have : some (-mateScore) = none := by
            simpa [hSome] using hNone
          cases this
      | false =>
          cases hRes : interpretResult gs with
          | ongoing =>
              have hMateFalse : isCheckmate gs = false := by
                unfold Rules.isCheckmate
                simp [hIn, hNo]
              have hStale : isStalemate gs = true := by
                unfold Rules.isStalemate
                simp [hIn, hNo]
              have hSome : terminalValue? gs = some 0 := by
                unfold terminalValue?
                simp [hMateFalse, hRes, hStale]
              have : some 0 = none := by
                simpa [hSome] using hNone
              cases this
          | whiteWin =>
              have hMateFalse : isCheckmate gs = false := by
                unfold Rules.isCheckmate
                simp [hIn, hNo]
              have hSome :
                  terminalValue? gs = some (winnerColorScore gs.toMove Color.White) := by
                unfold terminalValue?
                simp [hMateFalse, hRes]
              have : some (winnerColorScore gs.toMove Color.White) = none := by
                simpa [hSome] using hNone
              cases this
          | blackWin =>
              have hMateFalse : isCheckmate gs = false := by
                unfold Rules.isCheckmate
                simp [hIn, hNo]
              have hSome :
                  terminalValue? gs = some (winnerColorScore gs.toMove Color.Black) := by
                unfold terminalValue?
                simp [hMateFalse, hRes]
              have : some (winnerColorScore gs.toMove Color.Black) = none := by
                simpa [hSome] using hNone
              cases this
          | drawAuto _ =>
              have hMateFalse : isCheckmate gs = false := by
                unfold Rules.isCheckmate
                simp [hIn, hNo]
              have hSome : terminalValue? gs = some 0 := by
                unfold terminalValue?
                simp [hMateFalse, hRes]
              have : some 0 = none := by
                simpa [hSome] using hNone
              cases this
          | drawClaim _ =>
              have hMateFalse : isCheckmate gs = false := by
                unfold Rules.isCheckmate
                simp [hIn, hNo]
              have hSome : terminalValue? gs = some 0 := by
                unfold terminalValue?
                simp [hMateFalse, hRes]
              have : some 0 = none := by
                simpa [hSome] using hNone
              cases this
    cases hContra
  ·
    cases hNL : Rules.noLegalMoves gs with
    | true =>
        cases hNo hNL
    | false =>
        rfl

theorem terminalValue?_none_implies_allLegalMoves_nonempty (gs : GameState) :
    terminalValue? gs = none → allLegalMoves gs ≠ [] := by
  intro hNone
  have hNo : Rules.noLegalMoves gs = false := terminalValue?_none_implies_noLegalMoves_false gs hNone
  unfold Rules.noLegalMoves at hNo
  -- `List.isEmpty = false` implies nonempty.
  cases hMoves : allLegalMoves gs with
  | nil =>
      simp [hMoves] at hNo
  | cons m ms =>
      simp [hMoves]

private def scoreAt (d : Nat) (gs : GameState) (m : Move) : Int :=
  -(minimaxValue d (GameState.playMove gs m))

private theorem scoreAt_bounds (d : Nat) (gs : GameState) (m : Move)
    (hBounds : -mateScore ≤ minimaxValue d (GameState.playMove gs m) ∧
      minimaxValue d (GameState.playMove gs m) ≤ mateScore) :
    -mateScore ≤ scoreAt d gs m ∧ scoreAt d gs m ≤ mateScore := by
  constructor
  · -- lower: from upper bound on child
    have hUpper := hBounds.2
    have : -mateScore ≤ -(minimaxValue d (GameState.playMove gs m)) := by
      -- `x ≤ mateScore` -> `-mateScore ≤ -x`
      simpa using (Int.neg_le_neg hUpper)
    simpa [scoreAt]
  · -- upper: from lower bound on child
    have hLower := hBounds.1
    have : -(minimaxValue d (GameState.playMove gs m)) ≤ mateScore := by
      simpa using (Int.neg_le_neg hLower)
    simpa [scoreAt]

private theorem foldl_max_preserves_upper
    (ms : List Move) (best0 : Int) (hi0 : best0 ≤ mateScore)
    (score : Move → Int) (hScoreHi : ∀ m, m ∈ ms → score m ≤ mateScore) :
    (ms.foldl (fun best m => if score m > best then score m else best) best0) ≤ mateScore := by
  induction ms generalizing best0 with
  | nil =>
      simpa using hi0
  | cons m ms ih =>
      have hScoreHiHere : score m ≤ mateScore := hScoreHi m (by simp)
      by_cases hBetter : score m > best0
      ·
        have hi' : score m ≤ mateScore := hScoreHiHere
        simpa [List.foldl, hBetter] using ih (best0 := score m) hi' (by
          intro m' hm'
          exact hScoreHi m' (by simp [hm']))
      ·
        simpa [List.foldl, hBetter] using ih (best0 := best0) hi0 (by
          intro m' hm'
          exact hScoreHi m' (by simp [hm']))

private theorem foldl_max_preserves_lower
    (ms : List Move) (best0 : Int) (lo0 : -mateScore ≤ best0)
    (score : Move → Int) (hScoreLo : ∀ m, m ∈ ms → -mateScore ≤ score m) :
    -mateScore ≤ (ms.foldl (fun best m => if score m > best then score m else best) best0) := by
  induction ms generalizing best0 with
  | nil =>
      simpa using lo0
  | cons m ms ih =>
      have hScoreLoHere : -mateScore ≤ score m := hScoreLo m (by simp)
      by_cases hBetter : score m > best0
      ·
        simpa [List.foldl, hBetter] using ih (best0 := score m) hScoreLoHere (by
          intro m' hm'
          exact hScoreLo m' (by simp [hm']))
      ·
        simpa [List.foldl, hBetter] using ih (best0 := best0) lo0 (by
          intro m' hm'
          exact hScoreLo m' (by simp [hm']))

theorem minimaxValue_bounds (depth : Nat) (gs : GameState) :
    -mateScore ≤ minimaxValue depth gs ∧ minimaxValue depth gs ≤ mateScore := by
  induction depth generalizing gs with
  | zero =>
      exact minimaxValue_zero_bounds gs
  | succ d ih =>
      cases hTerm : terminalValue? gs with
      | some v =>
          -- Terminal case: directly bounded.
          have hb := terminalValue?_bounds gs v hTerm
          simpa [minimaxValue, hTerm] using hb
      | none =>
          -- Non-terminal: there is at least one legal move.
          have hNonempty : allLegalMoves gs ≠ [] := terminalValue?_none_implies_allLegalMoves_nonempty gs hTerm
          cases hMoves : allLegalMoves gs with
          | nil =>
              cases hNonempty (by simp [hMoves])
          | cons m0 ms =>
              -- Define the per-move score using the inductive bounds on children.
              let score : Move → Int := fun m => scoreAt d gs m
              have hScoreLo : ∀ mv, mv ∈ (m0 :: ms) → -mateScore ≤ score mv := by
                intro m' hm'
                have hb := ih (gs := GameState.playMove gs m')
                have hbScore := (scoreAt_bounds d gs m' hb).1
                simpa [score] using hbScore
              have hScoreHi : ∀ mv, mv ∈ (m0 :: ms) → score mv ≤ mateScore := by
                intro m' hm'
                have hb := ih (gs := GameState.playMove gs m')
                have hbScore := (scoreAt_bounds d gs m' hb).2
                simpa [score] using hbScore
              -- Since there is at least one move, the fold won't stay at the `worst` initializer.
              let worst : Int := -mateScore - 1
              have hWorstHi : worst ≤ mateScore := by
                native_decide
              -- Fold upper bound.
              have hUp :
                  (List.foldl (fun best mv => if score mv > best then score mv else best) worst (m0 :: ms)) ≤ mateScore :=
                foldl_max_preserves_upper (ms := (m0 :: ms)) (best0 := worst) hWorstHi score hScoreHi
              -- Fold lower bound: start after first element (since score m > worst always).
              have hScoreFirstLo : -mateScore ≤ score m0 := hScoreLo m0 (by simp)
              have hScoreGtWorst : score m0 > worst := by
                -- From `-mateScore ≤ score m` and `worst < -mateScore`.
                have hWorstLt : worst < -mateScore := by
                  native_decide
                exact Int.lt_of_lt_of_le hWorstLt hScoreFirstLo
              have hFoldDrop :
                  (List.foldl (fun best mv => if score mv > best then score mv else best) worst (m0 :: ms)) =
                    (List.foldl (fun best mv => if score mv > best then score mv else best) (score m0) ms) := by
                have hLt : worst < score m0 := by
                  simpa using hScoreGtWorst
                simp [List.foldl, hLt]
              have hLowTail :
                  -mateScore ≤
                    (List.foldl (fun best mv => if score mv > best then score mv else best) (score m0) ms) :=
                foldl_max_preserves_lower (ms := ms) (best0 := score m0) hScoreFirstLo score (by
                  intro m' hm'
                  exact hScoreLo m' (by simp [hm']))
              have hLow :
                  -mateScore ≤
                    (List.foldl (fun best mv => if score mv > best then score mv else best) worst (m0 :: ms)) := by
                simpa [hFoldDrop] using hLowTail
              constructor
              ·
                -- `minimaxValue` at succ depth is that fold with initializer `worst`.
                simpa [minimaxValue, hTerm, hMoves, worst, score, scoreAt] using hLow
              ·
                simpa [minimaxValue, hTerm, hMoves, worst, score, scoreAt] using hUp

end Analysis
end Chess
