import Chess.Rules

namespace Chess
namespace Rules

def kingPiece (c : Color) : Piece :=
  { pieceType := PieceType.King, color := c }

/-- Board-level invariant: at least one king of the given color exists. -/
def kingExists (b : Board) (c : Color) : Prop :=
  ∃ k : Square, b.get k = some (kingPiece c)

theorem kingExists_kingSquare_isSome (b : Board) (c : Color) :
    kingExists b c →
    (kingSquare b c).isSome = true := by
  intro hEx
  rcases hEx with ⟨k, hk⟩
  unfold kingSquare
  -- Use the `find?_isSome` characterization.
  refine (List.find?_isSome).2 ?_
  refine ⟨k, Square.mem_all k, ?_⟩
  -- The predicate for `kingSquare` is true at `k`.
  simp [hk, kingPiece]

end Rules
end Chess

