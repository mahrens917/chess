import Chess.Analysis.Spec
import Chess.Analysis.TerminalValueLemmas

namespace Chess
namespace Analysis

open Rules

/-!
Dead-position consequences for the analysis `terminalValue?` policy.

This does **not** attempt to prove the chess-theoretic claim that `deadPosition`
implies “no mate is reachable”; it only proves that once `deadPosition = true`,
the analysis layer treats the position as an automatic draw (value `0`) via
`drawStatus`/`interpretResult`/`terminalValue?`.
-/

theorem drawStatus_autoDraw_of_deadPosition (gs : GameState) :
    Rules.deadPosition gs = true → (Rules.drawStatus gs).2.1 = true := by
  intro hDead
  unfold Rules.drawStatus
  -- Expand the auto-reasons list and show it contains `"dead position"`.
  have hMem :
      "dead position" ∈
        ([ (isStalemate gs, "stalemate")
          , (isSeventyFiveMoveDraw gs, "75-move")
          , (fivefoldRepetition gs, "fivefold repetition")
          , (insufficientMaterial gs, "insufficient material")
          , (deadPosition gs, "dead position") ]
          |>.filterMap (fun (b, msg) => if b then some msg else none)) := by
    refine (List.mem_filterMap.2 ?_)
    refine ⟨(deadPosition gs, "dead position"), ?_, ?_⟩
    · simp
    · simp [hDead]
  -- A list with a member is not empty, so `¬autoReasons.isEmpty = true`.
  have hNonempty :
      ([ (isStalemate gs, "stalemate")
          , (isSeventyFiveMoveDraw gs, "75-move")
          , (fivefoldRepetition gs, "fivefold repetition")
          , (insufficientMaterial gs, "insufficient material")
          , (deadPosition gs, "dead position") ]
          |>.filterMap (fun (b, msg) => if b then some msg else none)) ≠ [] := by
    intro hNil
    -- Contradiction: a list equal to `[]` has no members.
    have hMem' := hMem
    simp [hNil] at hMem'
  -- Rewrite `isEmpty` by cases and finish.
  cases hAR :
      ([ (isStalemate gs, "stalemate")
          , (isSeventyFiveMoveDraw gs, "75-move")
          , (fivefoldRepetition gs, "fivefold repetition")
          , (insufficientMaterial gs, "insufficient material")
          , (deadPosition gs, "dead position") ]
          |>.filterMap (fun (b, msg) => if b then some msg else none)) with
  | nil =>
      cases hNonempty hAR
  | cons a as =>
      simp

theorem interpretResult_of_deadPosition
    (gs : GameState) (hRes : gs.result = none) (hDead : Rules.deadPosition gs = true) :
    ∃ reasons, Rules.interpretResult gs = Rules.GameResult.drawAuto reasons := by
  unfold Rules.interpretResult
  simp [hRes]
  -- Unfold `drawStatus` and use the auto-draw fact.
  have hAuto : (Rules.drawStatus gs).2.1 = true :=
    drawStatus_autoDraw_of_deadPosition (gs := gs) hDead
  -- `simp` can reduce the `if autoDraw then ...` once it knows `autoDraw = true`.
  -- We keep the actual `reasons` existentially quantified.
  rcases hDS : Rules.drawStatus gs with ⟨hasDraw, autoDraw, claim, auto⟩
  -- Rewrite `autoDraw` using `hAuto` and finish.
  have hAuto' : autoDraw = true := by
    -- `hAuto` is about the nested projection; rewrite via the definitional equality for `hDS`.
    simpa [hDS] using hAuto
  refine ⟨auto, ?_⟩
  -- Now `interpretResult` reduces to `drawAuto auto`.
  simp [hAuto']

theorem terminalValue?_of_deadPosition
    (gs : GameState)
    (hRes : gs.result = none)
    (hMate : Rules.isCheckmate gs = false)
    (hDead : Rules.deadPosition gs = true) :
    terminalValue? gs = some 0 := by
  rcases interpretResult_of_deadPosition (gs := gs) hRes hDead with ⟨reasons, hEq⟩
  exact
    terminalValue?_of_interpretResult_drawAuto
      (gs := gs) (reasons := reasons) (hMate := hMate) hEq

theorem isCheckmate_false_of_terminalValue?_none (gs : GameState) :
    terminalValue? gs = none → Rules.isCheckmate gs = false := by
  intro hNone
  cases hMate : Rules.isCheckmate gs with
  | true =>
      have : (some (-mateScore) : Option Int) = none := by
        simpa [terminalValue?, hMate] using hNone
      cases this
  | false =>
      rfl

theorem deadPosition_false_of_terminalValue?_none
    (gs : GameState)
    (hRes : gs.result = none)
    (hNone : terminalValue? gs = none) :
    Rules.deadPosition gs = false := by
  have hMate : Rules.isCheckmate gs = false :=
    isCheckmate_false_of_terminalValue?_none (gs := gs) hNone
  cases hDead : Rules.deadPosition gs with
  | true =>
      have hSome : terminalValue? gs = some 0 :=
        terminalValue?_of_deadPosition (gs := gs) hRes hMate hDead
      have : (some 0 : Option Int) = none := by
        simpa [hSome] using hNone
      cases this
  | false =>
      rfl

end Analysis
end Chess
