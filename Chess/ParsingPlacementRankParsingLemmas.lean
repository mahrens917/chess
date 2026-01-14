import Chess.Parsing
import Chess.ParsingCharRoundtripProofs

namespace Chess
namespace Parsing

open Chess

theorem fenDigitValue?_pieceToChar (p : Piece) : fenDigitValue? (pieceToChar p) = none := by
  cases p with
  | mk pt c =>
      cases pt <;> cases c <;> native_decide

theorem pieceToChar_ne_zero (p : Piece) : pieceToChar p ≠ '0' := by
  cases p with
  | mk pt c =>
      cases pt <;> cases c <;> decide

theorem digitChar_succ_ne_zero (k : Nat) (hk : k ≤ 7) : digitChar (k + 1) ≠ '0' := by
  cases k with
  | zero =>
      decide
  | succ k =>
      have hk' : k ≤ 6 := Nat.le_of_succ_le_succ hk
      cases k with
      | zero => decide
      | succ k =>
          have hk'' : k ≤ 5 := Nat.le_of_succ_le_succ hk'
          cases k with
          | zero => decide
          | succ k =>
              have hk''' : k ≤ 4 := Nat.le_of_succ_le_succ hk''
              cases k with
              | zero => decide
              | succ k =>
                  have hk'''' : k ≤ 3 := Nat.le_of_succ_le_succ hk'''
                  cases k with
                  | zero => decide
                  | succ k =>
                      have hk''''' : k ≤ 2 := Nat.le_of_succ_le_succ hk''''
                      cases k with
                      | zero => decide
                      | succ k =>
                          have hk'''''' : k ≤ 1 := Nat.le_of_succ_le_succ hk'''''
                          cases k with
                          | zero => decide
                          | succ k =>
                              have hk''''''' : k ≤ 0 := Nat.le_of_succ_le_succ hk''''''
                              have hkEq : k = 0 := Nat.eq_zero_of_le_zero hk'''''''
                              subst hkEq
                              decide

theorem parsePlacementRankChars_digitChar_succ (rank file k : Nat) (cs : List Char)
    (acc : List (Square × Piece)) (hk : k ≤ 7) :
    parsePlacementRankChars rank file (digitChar (k + 1) :: cs) acc =
      parsePlacementRankChars rank (file + (k + 1)) cs acc := by
  have h0 : digitChar (k + 1) ≠ '0' := digitChar_succ_ne_zero k hk
  have hDigit : fenDigitValue? (digitChar (k + 1)) = some (k + 1) :=
    fenDigitValue?_digitChar_succ k hk
  simp [parsePlacementRankChars, h0, hDigit]

theorem parsePlacementRankChars_digitChar (rank file n : Nat) (cs : List Char)
    (acc : List (Square × Piece)) (hn : n ≤ 8) (h0 : n ≠ 0) :
    parsePlacementRankChars rank file (digitChar n :: cs) acc =
      parsePlacementRankChars rank (file + n) cs acc := by
  rcases Nat.exists_eq_add_one_of_ne_zero h0 with ⟨k, hk⟩
  have hk7 : k ≤ 7 := by
    have hk8 : k + 1 ≤ 8 := by simpa [hk] using hn
    -- `k + 1 ≤ 8` implies `k ≤ 7`.
    have hk8' : Nat.succ k ≤ Nat.succ 7 := by
      simpa [Nat.succ_eq_add_one] using hk8
    exact Nat.le_of_succ_le_succ hk8'
  subst hk
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (parsePlacementRankChars_digitChar_succ (rank := rank) (file := file) (k := k) (cs := cs) (acc := acc) hk7)

theorem parsePlacementRankChars_pieceToChar (rank file : Nat) (p : Piece) (cs : List Char)
    (acc : List (Square × Piece)) (hFile : file < 8) :
    parsePlacementRankChars rank file (pieceToChar p :: cs) acc =
      parsePlacementRankChars rank (file + 1) cs ((Square.mkUnsafe file rank, p) :: acc) := by
  -- Unfold one step of the parser and discharge digit/piece branches.
  have h0 : pieceToChar p ≠ '0' := pieceToChar_ne_zero p
  have hDigit : fenDigitValue? (pieceToChar p) = none := fenDigitValue?_pieceToChar p
  have hPiece : pieceFromChar (pieceToChar p) = some p := pieceFromChar_pieceToChar p
  have hNotGe : ¬file ≥ 8 := Nat.not_le_of_lt hFile
  simp [parsePlacementRankChars, h0, hDigit, hPiece, hNotGe]

end Parsing
end Chess
