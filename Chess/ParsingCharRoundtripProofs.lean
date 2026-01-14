import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

theorem pieceFromChar_pieceToChar (p : Piece) : pieceFromChar (pieceToChar p) = some p := by
  cases p with
  | mk pt c =>
      cases pt <;> cases c <;> native_decide

theorem fenDigitValue?_digitChar_succ (k : Nat) (hk : k ≤ 7) :
    fenDigitValue? (digitChar (k + 1)) = some (k + 1) := by
  cases k with
  | zero => simp [fenDigitValue?, digitChar]
  | succ k =>
      have hk' : k ≤ 6 := Nat.le_of_succ_le_succ hk
      cases k with
      | zero => simp [fenDigitValue?, digitChar]
      | succ k =>
          have hk'' : k ≤ 5 := Nat.le_of_succ_le_succ hk'
          cases k with
          | zero => simp [fenDigitValue?, digitChar]
          | succ k =>
              have hk''' : k ≤ 4 := Nat.le_of_succ_le_succ hk''
              cases k with
              | zero => simp [fenDigitValue?, digitChar]
              | succ k =>
                  have hk'''' : k ≤ 3 := Nat.le_of_succ_le_succ hk'''
                  cases k with
                  | zero => simp [fenDigitValue?, digitChar]
                  | succ k =>
                      have hk''''' : k ≤ 2 := Nat.le_of_succ_le_succ hk''''
                      cases k with
                      | zero => simp [fenDigitValue?, digitChar]
                      | succ k =>
                          have hk'''''' : k ≤ 1 := Nat.le_of_succ_le_succ hk'''''
                          cases k with
                          | zero => simp [fenDigitValue?, digitChar]
                          | succ k =>
                              have hk''''''' : k ≤ 0 := Nat.le_of_succ_le_succ hk''''''
                              have hkEq : k = 0 := Nat.eq_zero_of_le_zero hk'''''''
                              subst hkEq
                              simp [fenDigitValue?, digitChar]

theorem fenDigitValue?_digitChar (n : Nat) (hn : n ≤ 8) (h0 : n ≠ 0) :
    fenDigitValue? (digitChar n) = some n := by
  rcases Nat.exists_eq_add_one_of_ne_zero h0 with ⟨k, rfl⟩
  have hk7 : k ≤ 7 := by
    have hk8 : k + 1 ≤ 8 := by simpa using hn
    have hk8' : Nat.succ k ≤ Nat.succ 7 := by
      simpa [Nat.succ_eq_add_one] using hk8
    exact Nat.le_of_succ_le_succ hk8'
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    fenDigitValue?_digitChar_succ k hk7

end Parsing
end Chess
