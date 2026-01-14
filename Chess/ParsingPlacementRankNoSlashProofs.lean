import Chess.Parsing
import Chess.ParsingPlacementRoundtripProofs
import Chess.ParsingPlacementNoSlashProofs

namespace Chess
namespace Parsing

open Chess

theorem rankToFenCharsAux_no_slash (board : Board) (rank file emptyCount : Nat)
    (hFile : file ≤ 8) (hCount : emptyCount ≤ file) :
    '/' ∉ rankToFenCharsAux board rank file emptyCount := by
  -- Induct on the remaining files (`8 - file`).
  induction hK : (8 - file) generalizing file emptyCount with
  | zero =>
      have hge : 8 ≤ file := Nat.le_of_sub_eq_zero hK
      have hEq : file = 8 := Nat.le_antisymm hFile hge
      subst hEq
      have hLe8 : emptyCount ≤ 8 := by simpa using hCount
      by_cases h0 : emptyCount = 0
      · subst h0
        simp [rankToFenCharsAux]
      · have hNe : digitChar emptyCount ≠ '/' := digitChar_ne_slash_of_le8 emptyCount hLe8
        intro hm
        simp [rankToFenCharsAux, h0] at hm
        exact hNe hm.symm
  | succ k ih =>
      have hlt : file < 8 := Nat.lt_of_sub_eq_succ hK
      have hFile' : file + 1 ≤ 8 := Nat.succ_le_of_lt hlt
      have hK' : 8 - (file + 1) = k := by
        calc
          8 - (file + 1) = 8 - Nat.succ file := by rfl
          _ = (8 - file).pred := by simpa using (Nat.sub_succ 8 file)
          _ = (Nat.succ k).pred := by simp [hK]
          _ = k := by simp
      cases hOcc : board (Square.mkUnsafe file rank) with
      | none =>
          have hCount' : emptyCount + 1 ≤ file + 1 := Nat.succ_le_succ hCount
          have hRec :
              '/' ∉ rankToFenCharsAux board rank (file + 1) (emptyCount + 1) :=
            ih (file := file + 1) (emptyCount := emptyCount + 1) hFile' hCount' hK'
          -- `rankToFenCharsAux` emits only the recursive tail on an empty square.
          unfold rankToFenCharsAux
          simpa [hlt, hOcc] using hRec
      | some p =>
          have hNePiece : pieceToChar p ≠ '/' := pieceToChar_ne_slash p
          have hRec :
              '/' ∉ rankToFenCharsAux board rank (file + 1) 0 :=
            ih (file := file + 1) (emptyCount := 0) hFile' (Nat.zero_le _) hK'
          by_cases h0 : emptyCount = 0
          · subst h0
            intro hm
            unfold rankToFenCharsAux at hm
            simp [hlt, hOcc] at hm
            rcases hm with hm | hm
            · exact hNePiece hm.symm
            exact hRec hm
          · have hLe8 : emptyCount ≤ 8 := Nat.le_trans hCount hFile
            have hNeDigit : digitChar emptyCount ≠ '/' := digitChar_ne_slash_of_le8 emptyCount hLe8
            intro hm
            unfold rankToFenCharsAux at hm
            simp [hlt, hOcc, h0] at hm
            rcases hm with hm | hm
            · exact hNeDigit hm.symm
            rcases hm with hm | hm
            · exact hNePiece hm.symm
            exact hRec hm

theorem rankToFenChars_no_slash (board : Board) (rank : Nat) :
    '/' ∉ rankToFenChars board rank := by
  unfold rankToFenChars
  simpa using
    (rankToFenCharsAux_no_slash (board := board) (rank := rank) (file := 0) (emptyCount := 0)
      (by decide) (by decide))

theorem splitPlacementChars_boardToFenPlacement (board : Board) :
    splitPlacementChars (boardToFenPlacement board).toList =
      (List.range 8).reverse.map (fun r => rankToFenChars board r) := by
  -- Reduce `boardToFenPlacement` to the list-level join.
  unfold boardToFenPlacement
  simp [String.toList_ofList]
  -- Now apply the join/split inversion theorem.
  let ranks : List (List Char) :=
    (List.range 8).reverse.map (fun r => rankToFenChars board r)
  have hne : ranks ≠ [] := by
    simp [ranks]
  have hNoSlash : ∀ r, r ∈ ranks → '/' ∉ r := by
    intro r hr
    rcases (List.mem_map.1 hr) with ⟨rNat, hrNat, rfl⟩
    exact rankToFenChars_no_slash board rNat
  simpa [ranks] using splitPlacementChars_joinPlacementChars (ranks := ranks) hne hNoSlash

end Parsing
end Chess
