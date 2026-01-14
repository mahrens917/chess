import Init.Data.Fin.Basic
import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

theorem pieceToChar_ne_slash (p : Piece) : pieceToChar p ≠ '/' := by
  cases p with
  | mk pt c =>
      cases pt <;> cases c <;> decide

theorem digitChar_ne_slash_of_le8 (n : Nat) (hn : n ≤ 8) : digitChar n ≠ '/' := by
  -- Convert `n ≤ 8` to a `Fin 9` and exhaust its cases.
  have hn9 : n < 9 := Nat.lt_succ_of_le hn
  let f : Fin 9 := ⟨n, hn9⟩
  have : digitChar f.val ≠ '/' := by
    -- `f.val` ranges over `0..8`.
    refine Fin.cases (motive := fun i : Fin 9 => digitChar i.val ≠ '/') ?_ ?_ f
    · decide
    · intro i
      refine Fin.cases (motive := fun i : Fin 8 => digitChar i.succ.val ≠ '/') ?_ ?_ i
      · decide
      · intro j
        refine Fin.cases (motive := fun j : Fin 7 => digitChar j.succ.succ.val ≠ '/') ?_ ?_ j
        · decide
        · intro k
          refine Fin.cases (motive := fun k : Fin 6 => digitChar k.succ.succ.succ.val ≠ '/') ?_ ?_ k
          · decide
          · intro l
            refine Fin.cases (motive := fun l : Fin 5 => digitChar l.succ.succ.succ.succ.val ≠ '/') ?_ ?_ l
            · decide
            · intro m
              refine Fin.cases (motive := fun m : Fin 4 => digitChar m.succ.succ.succ.succ.succ.val ≠ '/') ?_ ?_ m
              · decide
              · intro r
                refine Fin.cases (motive := fun r : Fin 3 => digitChar r.succ.succ.succ.succ.succ.succ.val ≠ '/') ?_ ?_ r
                · decide
                · intro s
                  refine Fin.cases (motive := fun s : Fin 2 => digitChar s.succ.succ.succ.succ.succ.succ.succ.val ≠ '/') ?_ ?_ s
                  · decide
                  · intro t
                    refine Fin.cases (motive := fun t : Fin 1 => digitChar t.succ.succ.succ.succ.succ.succ.succ.succ.val ≠ '/') ?_ ?_ t
                    · decide
                    · intro u
                      -- `Fin 0` has no inhabitants.
                      exact (False.elim (Nat.not_lt_zero _ u.isLt))
  simpa [f] using this

end Parsing
end Chess
