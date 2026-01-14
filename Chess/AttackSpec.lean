import Chess.Rules
import Chess.Movement

namespace Chess
namespace Rules

/-!
Prop-level attack specification corresponding to the executable `pieceAttacksSquare`.

This is *not* a “FIDE-correctness” theorem; it is a Bool/Prop bridge that makes it easier to
state and prove properties of `inCheck` and related predicates.
-/

/-- Prop-level “attack” predicate aligned with `pieceAttacksSquare`. -/
def attacksSpec (b : Board) (p : Piece) (source target : Square) : Prop :=
  match p.pieceType with
  | PieceType.King =>
      Movement.isKingStep source target
  | PieceType.Queen =>
      Movement.isQueenMove source target ∧ pathClear b source target = true
  | PieceType.Rook =>
      Movement.isRookMove source target ∧ pathClear b source target = true
  | PieceType.Bishop =>
      Movement.isDiagonal source target ∧ pathClear b source target = true
  | PieceType.Knight =>
      Movement.isKnightMove source target
  | PieceType.Pawn =>
      Movement.isPawnCapture p.color source target

theorem pieceAttacksSquare_eq_true_iff_attacksSpec
    (b : Board) (p : Piece) (source target : Square) :
    pieceAttacksSquare b p source target = true ↔ attacksSpec b p source target := by
  cases hPt : p.pieceType <;>
    simp [pieceAttacksSquare, attacksSpec, hPt, Bool.and_eq_true,
      Movement.isKingStepBool_eq_true_iff_isKingStep,
      Movement.isKnightMoveBool_eq_true_iff_isKnightMove]

theorem anyAttacksSquare_eq_true_iff_exists_attacker
    (b : Board) (target : Square) (byColor : Color) :
    anyAttacksSquare b target byColor = true ↔
      ∃ sq p,
        sq ∈ allSquares ∧
        b sq = some p ∧
        p.color = byColor ∧
        attacksSpec b p sq target := by
  unfold anyAttacksSquare
  -- Convert `List.any` into an existential and unpack the `match` branches.
  constructor
  · intro hAny
    rcases (List.any_eq_true).1 hAny with ⟨sq, hSqMem, hSq⟩
    cases hAt : b sq with
    | none =>
        cases (show False by simpa [hAt] using hSq)
    | some p =>
        have hAnd : p.color = byColor ∧ pieceAttacksSquare b p sq target = true := by
          -- `p.color = byColor && ... = true` splits into both components.
          have : (p.color = byColor && pieceAttacksSquare b p sq target) = true := by
            simpa [hAt] using hSq
          have hPair :
              decide (p.color = byColor) = true ∧ pieceAttacksSquare b p sq target = true :=
            Eq.mp (Bool.and_eq_true (decide (p.color = byColor)) (pieceAttacksSquare b p sq target)) this
          have hColor : p.color = byColor :=
            Eq.mp (decide_eq_true_eq (p := p.color = byColor)) hPair.1
          exact ⟨hColor, hPair.2⟩
        refine ⟨sq, p, hSqMem, hAt, hAnd.1, ?_⟩
        exact (pieceAttacksSquare_eq_true_iff_attacksSpec b p sq target).1 hAnd.2
  · rintro ⟨sq, p, hSqMem, hAt, hColor, hAtk⟩
    apply (List.any_eq_true).2
    refine ⟨sq, hSqMem, ?_⟩
    have hAtkBool : pieceAttacksSquare b p sq target = true :=
      (pieceAttacksSquare_eq_true_iff_attacksSpec b p sq target).2 hAtk
    have : (p.color = byColor && pieceAttacksSquare b p sq target) = true := by
      have : decide (p.color = byColor) = true ∧ pieceAttacksSquare b p sq target = true :=
        ⟨Eq.mpr (decide_eq_true_eq (p := p.color = byColor)) hColor, hAtkBool⟩
      exact
        Eq.mpr (Bool.and_eq_true (decide (p.color = byColor)) (pieceAttacksSquare b p sq target)) this
    simpa [hAt] using this

theorem inCheck_eq_true_iff_exists_attacker (b : Board) (c : Color) :
    inCheck b c = true ↔
      ∃ kingSq,
        kingSquare b c = some kingSq ∧
        (∃ sq p,
          sq ∈ allSquares ∧
          b sq = some p ∧
          p.color = c.opposite ∧
          attacksSpec b p sq kingSq) := by
  unfold inCheck
  cases hK : kingSquare b c with
  | none =>
      simp [hK]
  | some kingSq =>
      constructor
      · intro h
        refine ⟨kingSq, rfl, ?_⟩
        have : anyAttacksSquare b kingSq c.opposite = true := by
          simpa [hK] using h
        exact (anyAttacksSquare_eq_true_iff_exists_attacker b kingSq c.opposite).1 this
      · rintro ⟨kingSq', hK', hAtk⟩
        have hEq : kingSq' = kingSq := by
          cases hK'
          rfl
        cases hEq
        have : anyAttacksSquare b kingSq c.opposite = true :=
          (anyAttacksSquare_eq_true_iff_exists_attacker b kingSq c.opposite).2 hAtk
        simpa [hK] using this

end Rules
end Chess
