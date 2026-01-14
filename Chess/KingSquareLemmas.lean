import Init.Data.List.Find
import Chess.KingInvariants

namespace Chess
namespace Rules

theorem piece_eq_kingPiece_of_pieceType_color (p : Piece) (c : Color)
    (hType : p.pieceType = PieceType.King) (hColor : p.color = c) :
    p = kingPiece c := by
  cases p
  simp [kingPiece] at hType hColor
  subst hType
  subst hColor
  rfl

theorem kingSquare_eq_some_of_uniqueKing
    (b : Board) (c : Color) (k : Square)
    (hAt : b.get k = some (kingPiece c))
    (hUnique : ∀ sq, b.get sq = some (kingPiece c) → sq = k) :
    kingSquare b c = some k := by
  -- Existence of a king yields `isSome = true`.
  have hExists : kingExists b c := ⟨k, by simpa [kingPiece] using hAt⟩
  have hIsSomeBool : (kingSquare b c).isSome = true :=
    kingExists_kingSquare_isSome b c hExists
  -- Now determine which square `find?` returned using uniqueness.
  unfold kingSquare at ⊢
  let pred : Square → Bool := fun sq =>
    match b.get sq with
    | some p => decide (p.pieceType = PieceType.King) && decide (p.color = c)
    | none => false
  have hIsSome : (allSquares.find? pred).isSome = true := by
    simpa [kingSquare, pred] using hIsSomeBool
  cases hFind : allSquares.find? pred with
  | none =>
      -- Contradiction: `isSome` would be `false`.
      have : False := by
        -- In the `none` branch, `.isSome` is definitional `false`.
        have : (none : Option Square).isSome = true := by simpa [hFind] using hIsSome
        simpa using this
      cases this
  | some found =>
      have hPred : pred found = true := by
        exact List.find?_some (p := pred) (l := allSquares) (a := found) (by simpa [allSquares] using hFind)
      have hAtFound : b.get found = some (kingPiece c) := by
        cases hB : b.get found with
        | none =>
            cases (show False by simpa [pred, hB] using hPred)
        | some p =>
            have hAnd :
                decide (p.pieceType = PieceType.King) = true ∧ decide (p.color = c) = true := by
              have :
                  (decide (p.pieceType = PieceType.King) && decide (p.color = c)) = true := by
                simpa [pred, hB] using hPred
              exact
                Eq.mp (Bool.and_eq_true (decide (p.pieceType = PieceType.King)) (decide (p.color = c))) this
            have hType : p.pieceType = PieceType.King :=
              Eq.mp (decide_eq_true_eq (p := p.pieceType = PieceType.King)) hAnd.1
            have hColor : p.color = c :=
              Eq.mp (decide_eq_true_eq (p := p.color = c)) hAnd.2
            have hp : p = kingPiece c :=
              piece_eq_kingPiece_of_pieceType_color p c hType hColor
            simp [hB, hp]
      have hEq : found = k := hUnique found hAtFound
      subst hEq
      simpa [pred, hFind]

end Rules
end Chess
