import Chess.Analysis.Spec

namespace Chess
namespace Analysis

open Rules

/-!
Small reusable lemmas about `terminalValue?`.

These are meant to keep later analysis proofs (minimax/alpha-beta/repetition handling)
from having to repeatedly unfold and re-simplify the `terminalValue?` policy.
-/

theorem terminalValue?_eq_some_negMateScore_of_isCheckmate (gs : GameState) :
    Rules.isCheckmate gs = true → terminalValue? gs = some (-mateScore) := by
  intro hMate
  unfold terminalValue?
  simp [hMate]

theorem terminalValue?_of_interpretResult_drawAuto
    (gs : GameState) (reasons : List String)
    (hMate : Rules.isCheckmate gs = false)
    (hRes : Rules.interpretResult gs = Rules.GameResult.drawAuto reasons) :
    terminalValue? gs = some 0 := by
  unfold terminalValue?
  simp [hMate, hRes]

theorem terminalValue?_of_interpretResult_drawClaim
    (gs : GameState) (reasons : List String)
    (hMate : Rules.isCheckmate gs = false)
    (hRes : Rules.interpretResult gs = Rules.GameResult.drawClaim reasons) :
    terminalValue? gs = some 0 := by
  unfold terminalValue?
  simp [hMate, hRes]

theorem terminalValue?_of_interpretResult_ongoing_of_isStalemate
    (gs : GameState)
    (hMate : Rules.isCheckmate gs = false)
    (hRes : Rules.interpretResult gs = Rules.GameResult.ongoing)
    (hStale : Rules.isStalemate gs = true) :
    terminalValue? gs = some 0 := by
  unfold terminalValue?
  simp [hMate, hRes, hStale]

end Analysis
end Chess

