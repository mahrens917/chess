import Chess.Rules

namespace Chess
namespace Rules

/-!
Prop-level specifications for draw-related helpers.

These are small Bool/Prop bridge lemmas intended for downstream proofs and test-time `#check`s.
-/

def isFiftyMoveDraw_spec (gs : GameState) : Prop :=
  gs.halfMoveClock ≥ 100

theorem isFiftyMoveDraw_iff (gs : GameState) :
    isFiftyMoveDraw gs = true ↔ isFiftyMoveDraw_spec gs := by
  simp [isFiftyMoveDraw, isFiftyMoveDraw_spec]

def isSeventyFiveMoveDraw_spec (gs : GameState) : Prop :=
  gs.halfMoveClock ≥ 150

theorem isSeventyFiveMoveDraw_iff (gs : GameState) :
    isSeventyFiveMoveDraw gs = true ↔ isSeventyFiveMoveDraw_spec gs := by
  simp [isSeventyFiveMoveDraw, isSeventyFiveMoveDraw_spec]

theorem seventyFive_implies_fifty (gs : GameState) :
    isSeventyFiveMoveDraw gs = true → isFiftyMoveDraw gs = true := by
  intro h75
  have h75' : gs.halfMoveClock ≥ 150 := (isSeventyFiveMoveDraw_iff gs).1 h75
  have h50' : gs.halfMoveClock ≥ 100 := Nat.le_trans (by decide : (100 : Nat) ≤ 150) h75'
  exact (isFiftyMoveDraw_iff gs).2 h50'

def threefoldRepetition_spec (gs : GameState) : Prop :=
  let snap := positionSnapshot gs
  let snaps := gs.history ++ [snap]
  snaps.count snap ≥ 3

theorem threefoldRepetition_iff (gs : GameState) :
    threefoldRepetition gs = true ↔ threefoldRepetition_spec gs := by
  simp [threefoldRepetition, threefoldRepetition_spec]

def fivefoldRepetition_spec (gs : GameState) : Prop :=
  let snap := positionSnapshot gs
  let snaps := gs.history ++ [snap]
  snaps.count snap ≥ 5

theorem fivefoldRepetition_iff (gs : GameState) :
    fivefoldRepetition gs = true ↔ fivefoldRepetition_spec gs := by
  simp [fivefoldRepetition, fivefoldRepetition_spec]

theorem fivefold_implies_threefold (gs : GameState) :
    fivefoldRepetition gs = true → threefoldRepetition gs = true := by
  intro h5
  have h5' : fivefoldRepetition_spec gs := (fivefoldRepetition_iff gs).1 h5
  -- `≥ 5` implies `≥ 3`.
  have h3' : threefoldRepetition_spec gs := by
    -- unfold the shared `snaps.count` term under both specs
    unfold fivefoldRepetition_spec at h5'
    unfold threefoldRepetition_spec
    simpa using (Nat.le_trans (by decide : (3 : Nat) ≤ 5) h5')
  exact (threefoldRepetition_iff gs).2 h3'

end Rules
end Chess
