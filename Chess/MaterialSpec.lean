import Chess.Rules

namespace Chess
namespace Rules

/-!
Rules-complete (implementation-exact) Prop-level specs for material-based draw helpers.

These are *not* claims of FIDE-semantic completeness; they are intended as stable
spec targets for proofs about the current executable predicates.
-/

abbrev insufficientMaterialExact (gs : GameState) : Prop :=
  insufficientMaterial gs = true

theorem insufficientMaterial_eq_true_iff (gs : GameState) :
    insufficientMaterial gs = true ↔ insufficientMaterialExact gs := by
  rfl

abbrev deadPositionHeuristic (gs : GameState) : Prop :=
  deadPosition gs = true

theorem deadPosition_eq_true_iff (gs : GameState) :
    deadPosition gs = true ↔ deadPositionHeuristic gs := by
  rfl

end Rules
end Chess

