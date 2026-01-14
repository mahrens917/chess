import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

namespace NatString

theorem digitChar_ne_space_of_lt10 (d : Nat) (hd : d < 10) : Nat.digitChar d ≠ ' ' := by
  -- Convert `d < 10` to a `Fin 10` and exhaust its cases.
  let f : Fin 10 := ⟨d, hd⟩
  have : Nat.digitChar f.val ≠ ' ' := by
    refine Fin.cases (motive := fun i : Fin 10 => Nat.digitChar i.val ≠ ' ') ?_ ?_ f
    · decide
    · intro i
      refine Fin.cases (motive := fun i : Fin 9 => Nat.digitChar i.succ.val ≠ ' ') ?_ ?_ i
      · decide
      · intro j
        refine Fin.cases (motive := fun j : Fin 8 => Nat.digitChar j.succ.succ.val ≠ ' ') ?_ ?_ j
        · decide
        · intro k
          refine Fin.cases (motive := fun k : Fin 7 => Nat.digitChar k.succ.succ.succ.val ≠ ' ') ?_ ?_ k
          · decide
          · intro l
            refine Fin.cases (motive := fun l : Fin 6 => Nat.digitChar l.succ.succ.succ.succ.val ≠ ' ') ?_ ?_ l
            · decide
            · intro m
              refine Fin.cases (motive := fun m : Fin 5 => Nat.digitChar m.succ.succ.succ.succ.succ.val ≠ ' ') ?_ ?_ m
              · decide
              · intro n
                refine Fin.cases (motive := fun n : Fin 4 => Nat.digitChar n.succ.succ.succ.succ.succ.succ.val ≠ ' ') ?_ ?_ n
                · decide
                · intro r
                  refine Fin.cases (motive := fun r : Fin 3 => Nat.digitChar r.succ.succ.succ.succ.succ.succ.succ.val ≠ ' ') ?_ ?_ r
                  · decide
                  · intro s
                    refine Fin.cases (motive := fun s : Fin 2 => Nat.digitChar s.succ.succ.succ.succ.succ.succ.succ.succ.val ≠ ' ') ?_ ?_ s
                    · decide
                    · intro t
                      refine Fin.cases (motive := fun t : Fin 1 => Nat.digitChar t.succ.succ.succ.succ.succ.succ.succ.succ.succ.val ≠ ' ') ?_ ?_ t
                      · decide
                      · intro u
                        exact (False.elim (Nat.not_lt_zero _ u.isLt))
  simpa [f] using this

theorem toDigitsCore_no_space (fuel n : Nat) (ds : List Char) (hds : ' ' ∉ ds) :
    ' ' ∉ Nat.toDigitsCore 10 fuel n ds := by
  induction fuel generalizing n ds with
  | zero =>
      simpa [Nat.toDigitsCore] using hds
  | succ fuel ih =>
      have hdLt : n % 10 < 10 := Nat.mod_lt n (by decide : 0 < 10)
      have hdNe : Nat.digitChar (n % 10) ≠ ' ' := digitChar_ne_space_of_lt10 (n % 10) hdLt
      -- `Nat.toDigitsCore` uses the test `n < 10` (after unfolding), so split on it.
      by_cases hn : n < 10
      · -- Base case: the output is `digitChar (n % 10) :: ds`.
        intro hm
        -- Unfold and simplify the branch.
        simp [Nat.toDigitsCore, hn] at hm
        rcases hm with hmEq | hmTail
        · exact hdNe hmEq.symm
        · exact hds hmTail
      · -- Recursive case: the output is `toDigitsCore ... (n / 10) (digitChar (n % 10) :: ds)`.
        have hds' : ' ' ∉ Nat.digitChar (n % 10) :: ds := by
          intro hm
          simp at hm
          rcases hm with hmEq | hmTail
          · exact hdNe hmEq.symm
          · exact hds hmTail
        have hRec :
            ' ' ∉ Nat.toDigitsCore 10 fuel (n / 10) (Nat.digitChar (n % 10) :: ds) :=
          ih (n := n / 10) (ds := Nat.digitChar (n % 10) :: ds) hds'
        intro hm
        have hm' :
            ' ' ∈ Nat.toDigitsCore 10 fuel (n / 10) (Nat.digitChar (n % 10) :: ds) := by
          simpa [Nat.toDigitsCore, hn] using hm
        exact hRec hm'

theorem toDigits_no_space (n : Nat) : ' ' ∉ Nat.toDigits 10 n := by
  unfold Nat.toDigits
  simpa using toDigitsCore_no_space (fuel := n + 1) (n := n) (ds := []) (by simp)

theorem toString_no_space (n : Nat) : ' ' ∉ (toString n).toList := by
  -- `toString n` for `Nat` is `Nat.repr n`.
  change ' ' ∉ (Nat.repr n).toList
  -- `Nat.repr` is `String.ofList (Nat.toDigits 10 n)`.
  simp [Nat.repr, toDigits_no_space]

end NatString

end Parsing
end Chess
