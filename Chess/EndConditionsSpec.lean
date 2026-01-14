import Chess.Rules

namespace Chess
namespace Rules

/-!
Prop-level specifications for end-condition helpers (`isCheckmate`, `isStalemate`).

These theorems are intentionally lightweight: they bridge `Bool` helpers to corresponding `Prop`
statements so other proofs can reason with conjunctions/existentials instead of `&&`/`List.isEmpty`.
-/

def noLegalMovesSpec (gs : GameState) : Prop :=
  (allLegalMoves gs).isEmpty = true

def inCheckStatusSpec (gs : GameState) : Prop :=
  inCheck gs.board gs.toMove = true

def notInCheckStatusSpec (gs : GameState) : Prop :=
  inCheck gs.board gs.toMove = false

def isCheckmateSpec (gs : GameState) : Prop :=
  inCheckStatusSpec gs ∧ noLegalMovesSpec gs

def isStalemateSpec (gs : GameState) : Prop :=
  notInCheckStatusSpec gs ∧ noLegalMovesSpec gs

theorem noLegalMoves_iff_noLegalMovesSpec (gs : GameState) :
    noLegalMoves gs = true ↔ noLegalMovesSpec gs := by
  simp [noLegalMoves, noLegalMovesSpec]

theorem inCheckStatus_iff_inCheckStatusSpec (gs : GameState) :
    inCheckStatus gs = true ↔ inCheckStatusSpec gs := by
  simp [inCheckStatus, inCheckStatusSpec]

theorem isCheckmate_iff_isCheckmateSpec (gs : GameState) :
    isCheckmate gs = true ↔ isCheckmateSpec gs := by
  simp [isCheckmate, isCheckmateSpec, inCheckStatusSpec, noLegalMovesSpec, inCheckStatus, noLegalMoves]

theorem isStalemate_iff_isStalemateSpec (gs : GameState) :
    isStalemate gs = true ↔ isStalemateSpec gs := by
  simp [isStalemate, isStalemateSpec, notInCheckStatusSpec, noLegalMovesSpec, inCheckStatus, noLegalMoves]

end Rules
end Chess

