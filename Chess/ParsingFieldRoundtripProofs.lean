import Chess.Parsing

namespace Chess
namespace Parsing

open Chess

theorem parseActiveColor_roundtrip (c : Color) :
    parseActiveColor (if c = Color.White then "w" else "b") = .ok c := by
  cases c <;> native_decide

theorem parseCastlingRights_roundtrip (cr : CastlingRights) :
    parseCastlingRights (castlingToFen cr) = cr := by
  cases cr with
  | mk wK wQ bK bQ =>
      cases wK <;> cases wQ <;> cases bK <;> cases bQ <;> native_decide

theorem parseEnPassant_dash_roundtrip :
    parseEnPassant "-" = .ok none := by
  native_decide

theorem parseEnPassant_algebraic_roundtrip (sq : Square) :
    parseEnPassant sq.algebraic = .ok (some sq) := by
  let P : Square → Prop := fun s => parseEnPassant s.algebraic = .ok (some s)
  have hAll : Square.all.all (fun s => decide (P s)) = true := by
    native_decide
  have hMem : ∀ s, s ∈ Square.all → decide (P s) = true :=
    (List.all_eq_true).1 hAll
  have hDec : decide (P sq) = true := hMem sq (Square.mem_all sq)
  have hIff : (decide (P sq) = true) ↔ P sq :=
    Iff.of_eq (decide_eq_true_eq (p := P sq))
  exact hIff.1 hDec

end Parsing
end Chess
