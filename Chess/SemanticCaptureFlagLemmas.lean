import Chess.Spec
import Chess.Rules

namespace Chess
namespace Rules

theorem captureFlagConsistentWithEP_of_destinationFriendlyFree_and_captureFlagConsistent
    (gs : GameState) (m : Move) :
    destinationFriendlyFreeProp gs m →
    captureFlagConsistent gs m = true →
    captureFlagConsistentWithEP gs m := by
  intro hDest hCap
  unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
  unfold captureFlagConsistentWithEP
  cases hEP : m.isEnPassant with
  | true =>
      -- `captureFlagConsistent` forces `m.isCapture = true`.
      have hIsCap : m.isCapture = true := by
        simpa [captureFlagConsistent, hEP] using hCap
      -- RHS is true (because `m.isEnPassant`), so the spec reduces to `m.isCapture = true`.
      simp [hEP, hIsCap]
  | false =>
      cases hBoard : gs.board m.toSq with
      | none =>
          -- `captureFlagConsistent = true` implies `m.isCapture = false`.
          have hIsCap : m.isCapture = false := by
            simpa [captureFlagConsistent, hEP, hBoard] using hCap
          -- No piece on the destination, so the “enemy at dest” disjunct is false.
          simp [hEP, hBoard, hIsCap]
      | some p =>
          -- `captureFlagConsistent = true` implies `m.isCapture = true`.
          have hIsCap : m.isCapture = true := by
            simpa [captureFlagConsistent, hEP, hBoard] using hCap
          -- Destination is enemy because `destinationFriendlyFree = true`.
          have hEnemy : p.color ≠ m.piece.color := by
            -- With `destinationFriendlyFree`, a `some p` destination forces `p.color ≠ m.piece.color`.
            simp only [hBoard] at hDest
            exact of_decide_eq_true hDest
          -- Prove the iff: `isCapture = true` iff "enemy at dest".
          constructor
          · intro _h
            left
            refine ⟨p, ?_, hEnemy⟩
            simp only [hBoard]
          · intro hRhs
            -- Since `m.isEnPassant = false`, the RHS implies an enemy piece exists at destination,
            -- hence `m.isCapture = true`.
            rcases hRhs with hEnemyOr | hEPFalse
            · exact hIsCap
            · rw [hEP] at hEPFalse
              cases hEPFalse

theorem captureFlagConsistent_of_destinationFriendlyFree_and_captureFlagConsistentWithEP
    (gs : GameState) (m : Move) :
    destinationFriendlyFreeProp gs m →
    captureFlagConsistentWithEP gs m →
    captureFlagConsistent gs m = true := by
  intro hDest hSpec
  unfold destinationFriendlyFreeProp destinationFriendlyFree at hDest
  unfold captureFlagConsistentWithEP at hSpec
  cases hEP : m.isEnPassant with
  | true =>
      -- Spec forces `m.isCapture = true`.
      have hIsCap : m.isCapture = true := by
        have hRhs : (∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ (m.isEnPassant : Prop) :=
          Or.inr (by simp [hEP])
        exact hSpec.2 hRhs
      -- For EP, `captureFlagConsistent` is just `m.isCapture`.
      simp [captureFlagConsistent, hEP, hIsCap]
  | false =>
      cases hBoard : gs.board m.toSq with
      | none =>
          -- No piece at destination, so RHS of the spec is false, hence `isCapture = false`.
          have hIsCap : m.isCapture = false := by
            have hNoEnemy :
                ¬(∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) := by
              intro hEx
              rcases hEx with ⟨p, hAt, _hNe⟩
              simpa [hBoard] using hAt
            have hRhsFalse :
                ¬((∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ (m.isEnPassant : Prop)) := by
              intro hRhs
              rcases hRhs with hEx | hEP'
              · exact hNoEnemy hEx
              · cases (show False by simpa [hEP] using hEP')
            -- If `m.isCapture = true` we'd contradict the spec.
            cases hCap : m.isCapture with
            | false => simp [hCap]
            | true =>
                have : False := hRhsFalse (hSpec.1 (by simp [hCap]))
                cases this
          -- `captureFlagConsistent` requires `¬ isCapture`.
          simp [captureFlagConsistent, hEP, hBoard, hIsCap]
      | some p =>
          -- Destination is enemy because `destinationFriendlyFree = true`.
          have hEnemy : p.color ≠ m.piece.color := by
            simp only [hBoard] at hDest
            exact of_decide_eq_true hDest
          have hIsCap : m.isCapture = true := by
            have hRhs : (∃ q, gs.board m.toSq = some q ∧ q.color ≠ m.piece.color) ∨ (m.isEnPassant : Prop) := by
              left
              refine ⟨p, ?_, hEnemy⟩
              simp only [hBoard]
            exact hSpec.2 hRhs
          simp [captureFlagConsistent, hEP, hBoard, hIsCap]

end Rules
end Chess
