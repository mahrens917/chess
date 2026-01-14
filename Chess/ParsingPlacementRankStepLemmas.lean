import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

theorem rankToFenCharsAux_step_none (board : Board) (rank file emptyCount : Nat)
    (hFile : file < 8)
    (hGet : board.get (Square.mkUnsafe file rank) = none) :
    rankToFenCharsAux board rank file emptyCount =
      rankToFenCharsAux board rank (file + 1) (emptyCount + 1) := by
  generalize hRhs : rankToFenCharsAux board rank (file + 1) (emptyCount + 1) = rhs
  -- Unfold only the LHS occurrence.
  unfold rankToFenCharsAux
  -- Discharge the `file < 8` and `board.get` branches.
  simp [hFile, hGet]
  exact hRhs

theorem rankToFenCharsAux_step_some (board : Board) (rank file emptyCount : Nat) (p : Piece)
    (hFile : file < 8)
    (hGet : board.get (Square.mkUnsafe file rank) = some p) :
    rankToFenCharsAux board rank file emptyCount =
      (if emptyCount = 0 then [] else [digitChar emptyCount]) ++
        (pieceToChar p :: rankToFenCharsAux board rank (file + 1) 0) := by
  generalize hTail : rankToFenCharsAux board rank (file + 1) 0 = tail
  -- Unfold only the LHS occurrence.
  unfold rankToFenCharsAux
  -- Discharge the `file < 8` and `board.get` branches, then rewrite the recursive tail.
  simp [hFile, hGet, hTail]

theorem rankToFenCharsAux_done (board : Board) (rank file emptyCount : Nat)
    (hFile : ¬file < 8) :
    rankToFenCharsAux board rank file emptyCount =
      (if emptyCount = 0 then [] else [digitChar emptyCount]) := by
  unfold rankToFenCharsAux
  simp [hFile]

end Parsing
end Chess
