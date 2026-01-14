import Chess.Rules

namespace Chess
namespace Rules

@[simp] theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e).bind f = Except.error e := by
  rfl

@[simp] theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a).bind f = f a := by
  rfl

@[simp] theorem except_bind_error' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := by
  rfl

@[simp] theorem except_bind_ok' {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := by
  rfl

@[simp] theorem applyLegalMoves_nil (gs : GameState) :
    applyLegalMoves gs [] = Except.ok gs := by
  simp [applyLegalMoves]
  change (pure gs : Except String GameState) = Except.ok gs
  rfl

theorem applyLegalMoves_cons (gs : GameState) (m : Move) (ms : List Move) :
    applyLegalMoves gs (m :: ms) =
      (applyLegalMove gs m >>= fun gs' => applyLegalMoves gs' ms) := by
  simp [applyLegalMoves]

theorem applyLegalMoves_eq_ok_cons_iff (gs : GameState) (m : Move) (ms : List Move) (gs' : GameState) :
    applyLegalMoves gs (m :: ms) = Except.ok gs' ↔
      ∃ gs1, applyLegalMove gs m = Except.ok gs1 ∧ applyLegalMoves gs1 ms = Except.ok gs' := by
  constructor
  · intro h
    have h' :
        (applyLegalMove gs m >>= fun gs1 => applyLegalMoves gs1 ms) = Except.ok gs' := by
      simpa [applyLegalMoves_cons] using h
    cases hStep : applyLegalMove gs m with
    | error e =>
        have hContra0 :
            (Except.error e >>= fun gs1 => applyLegalMoves gs1 ms) = Except.ok gs' := by
          simpa [hStep] using h'
        have hContra : Except.error e = Except.ok gs' := by
          simpa using hContra0
        cases hContra
    | ok gs1 =>
        refine ⟨gs1, by simp [hStep], ?_⟩
        simpa [hStep] using h'
  · rintro ⟨gs1, hStep, hTail⟩
    -- `bind` on `Except.ok` is definitional.
    simpa [applyLegalMoves_cons, hStep] using hTail

end Rules
end Chess
