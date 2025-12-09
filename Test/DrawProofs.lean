import Chess.Rules

open Chess Chess.Rules

-- Verify the draw detection proofs are accessible and type-check

#check isFiftyMoveDraw_iff
#check isFiftyMoveDraw_spec
#check isSeventyFiveMoveDraw_iff
#check isSeventyFiveMoveDraw_spec
#check seventyFive_implies_fifty
#check threefoldRepetition_spec
#check threefoldRepetition_counts_current
#check fivefoldRepetition_spec
#check fivefold_implies_threefold

-- Test the basic specifications
example (gs : GameState) (h : gs.halfMoveClock ≥ 100) :
    isFiftyMoveDraw gs = true := by
  rw [isFiftyMoveDraw_iff]
  exact h

example (gs : GameState) (h : gs.halfMoveClock ≥ 150) :
    isSeventyFiveMoveDraw gs = true := by
  rw [isSeventyFiveMoveDraw_iff]
  exact h

example (gs : GameState) :
    isSeventyFiveMoveDraw gs = true → isFiftyMoveDraw gs = true :=
  seventyFive_implies_fifty gs

example (gs : GameState) :
    fivefoldRepetition gs = true → threefoldRepetition gs = true :=
  fivefold_implies_threefold gs
