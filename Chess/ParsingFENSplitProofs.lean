import Chess.Parsing
import Chess.ParsingPlacementRankNoSpaceProofs
import Chess.ParsingNatStringNoSpaceProofs

namespace Chess
namespace Parsing

open Chess

theorem algebraic_no_space (sq : Square) : ' ' ∉ sq.algebraic.toList := by
  let P : Square → Prop := fun s => ' ' ∉ s.algebraic.toList
  have hAll : Square.all.all (fun s => decide (P s)) = true := by
    native_decide
  have hMem : ∀ s, s ∈ Square.all → decide (P s) = true :=
    (List.all_eq_true).1 hAll
  have hDec : decide (P sq) = true := hMem sq (Square.mem_all sq)
  have hIff : (decide (P sq) = true) ↔ P sq :=
    Iff.of_eq (decide_eq_true_eq (p := P sq))
  exact hIff.1 hDec

theorem castlingToFen_no_space (cr : CastlingRights) : ' ' ∉ (castlingToFen cr).toList := by
  cases cr with
  | mk wK wQ bK bQ =>
      cases wK <;> cases wQ <;> cases bK <;> cases bQ <;> decide

theorem activeColorField_no_space (c : Color) :
    ' ' ∉ (if c = Color.White then "w" else "b").toList := by
  cases c <;> decide

theorem epField_no_space (ep : Option Square) :
    ' ' ∉ (ep.map (fun sq => sq.algebraic) |>.getD "-").toList := by
  cases ep with
  | none =>
      decide
  | some sq =>
      simpa using algebraic_no_space sq

theorem splitFenFieldsCharsAux_prefix (chars cur : List Char) (acc : List (List Char)) :
    splitFenFieldsCharsAux chars cur acc =
      acc.reverse ++ splitFenFieldsCharsAux chars cur [] := by
  induction chars generalizing cur acc with
  | nil =>
      simp [splitFenFieldsCharsAux]
  | cons c cs ih =>
      by_cases h : c = ' '
      · subst h
        have hCommit :=
          (ih (cur := []) (acc := cur.reverse :: acc))
        have hSingleton :=
          (ih (cur := []) (acc := [cur.reverse]))
        calc
          splitFenFieldsCharsAux (' ' :: cs) cur acc
              = splitFenFieldsCharsAux cs [] (cur.reverse :: acc) := by
                  simp [splitFenFieldsCharsAux]
          _ = (cur.reverse :: acc).reverse ++ splitFenFieldsCharsAux cs [] [] := by
                  simpa using hCommit
          _ = (acc.reverse ++ [cur.reverse]) ++ splitFenFieldsCharsAux cs [] [] := by
                  simp [List.reverse_cons, List.append_assoc]
          _ = acc.reverse ++ ([cur.reverse] ++ splitFenFieldsCharsAux cs [] []) := by
                  simp [List.append_assoc]
          _ = acc.reverse ++ splitFenFieldsCharsAux cs [] [cur.reverse] := by
                  simpa [List.reverse_cons, List.append_assoc] using
                    congrArg (fun t => acc.reverse ++ t) hSingleton.symm
          _ = acc.reverse ++ splitFenFieldsCharsAux (' ' :: cs) cur [] := by
                  simp [splitFenFieldsCharsAux]
      ·
        have hIH := ih (cur := c :: cur) (acc := acc)
        simpa [splitFenFieldsCharsAux, h] using hIH

theorem splitFenFieldsCharsAux_append_no_sep (xs ys : List Char) (cur : List Char) (acc : List (List Char))
    (hxs : ' ' ∉ xs) :
    splitFenFieldsCharsAux (xs ++ ys) cur acc =
      splitFenFieldsCharsAux ys (xs.reverse ++ cur) acc := by
  induction xs generalizing cur acc with
  | nil =>
      simp [splitFenFieldsCharsAux]
  | cons c cs ih =>
      have hc : c ≠ ' ' := by
        intro h
        apply hxs
        simp [h]
      have hcs : ' ' ∉ cs := by
        intro hm
        apply hxs
        simp [hm]
      have hIH := ih (cur := c :: cur) (acc := acc) hcs
      calc
        splitFenFieldsCharsAux ((c :: cs) ++ ys) cur acc
            = splitFenFieldsCharsAux (cs ++ ys) (c :: cur) acc := by
                simp [List.cons_append, splitFenFieldsCharsAux, hc]
        _ = splitFenFieldsCharsAux ys (cs.reverse ++ (c :: cur)) acc := by
                simpa using hIH
        _ = splitFenFieldsCharsAux ys ((c :: cs).reverse ++ cur) acc := by
                simp [List.reverse_cons, List.append_assoc]

theorem splitFenFieldsCharsAux_of_no_sep (xs cur : List Char) (hxs : ' ' ∉ xs) :
    splitFenFieldsCharsAux xs cur [] = [(xs.reverse ++ cur).reverse] := by
  induction xs generalizing cur with
  | nil =>
      simp [splitFenFieldsCharsAux]
  | cons c cs ih =>
      have hc : c ≠ ' ' := by
        intro h
        apply hxs
        simp [h]
      have hcs : ' ' ∉ cs := by
        intro hm
        apply hxs
        simp [hm]
      simpa [splitFenFieldsCharsAux, hc, List.reverse_cons, List.append_assoc] using
        (ih (cur := c :: cur) hcs)

theorem splitFenFieldsChars_of_no_sep (xs : List Char) (hxs : ' ' ∉ xs) :
    splitFenFieldsChars xs = [xs] := by
  simpa [splitFenFieldsChars] using
    (splitFenFieldsCharsAux_of_no_sep (xs := xs) (cur := []) hxs)

theorem splitFenFieldsChars_append_sep (xs ys : List Char) (hxs : ' ' ∉ xs) :
    splitFenFieldsChars (xs ++ ' ' :: ys) = xs :: splitFenFieldsChars ys := by
  have hMove :=
    splitFenFieldsCharsAux_append_no_sep (xs := xs) (ys := ' ' :: ys) (cur := []) (acc := []) hxs
  have hPrefix :
      splitFenFieldsCharsAux (xs ++ ' ' :: ys) [] [] = splitFenFieldsCharsAux (' ' :: ys) xs.reverse [] := by
    simpa [List.append_assoc] using hMove
  have hAfter :
      splitFenFieldsCharsAux (xs ++ ' ' :: ys) [] [] = splitFenFieldsCharsAux ys [] [xs] := by
    simp [splitFenFieldsCharsAux, hPrefix]
  calc
    splitFenFieldsChars (xs ++ ' ' :: ys)
        = splitFenFieldsCharsAux (xs ++ ' ' :: ys) [] [] := by rfl
    _ = splitFenFieldsCharsAux ys [] [xs] := by simp [hAfter]
    _ = [xs].reverse ++ splitFenFieldsCharsAux ys [] [] := by
          simpa using (splitFenFieldsCharsAux_prefix (chars := ys) (cur := []) (acc := [xs]))
    _ = xs :: splitFenFieldsChars ys := by rfl

theorem splitFenFieldsChars_joinPlacementChars (parts : List (List Char))
    (hne : parts ≠ []) (hNoSpace : ∀ p, p ∈ parts → ' ' ∉ p) :
    splitFenFieldsChars (joinPlacementChars ' ' parts) = parts := by
  induction parts with
  | nil =>
      cases hne rfl
  | cons p ps ih =>
      cases ps with
      | nil =>
          have hp : ' ' ∉ p := hNoSpace p (by simp)
          simp [joinPlacementChars, splitFenFieldsChars_of_no_sep p hp]
      | cons p2 ps2 =>
          have hp : ' ' ∉ p := hNoSpace p (by simp)
          have hne' : (p2 :: ps2) ≠ [] := by simp
          have hNoSpace' : ∀ p', p' ∈ (p2 :: ps2) → ' ' ∉ p' := by
            intro p' hp'
            exact hNoSpace p' (by simp [hp'])
          have ih' : splitFenFieldsChars (joinPlacementChars ' ' (p2 :: ps2)) = (p2 :: ps2) :=
            ih hne' hNoSpace'
          calc
            splitFenFieldsChars (joinPlacementChars ' ' (p :: p2 :: ps2))
                = splitFenFieldsChars (p ++ ' ' :: joinPlacementChars ' ' (p2 :: ps2)) := by
                    simp [joinPlacementChars]
            _ = p :: splitFenFieldsChars (joinPlacementChars ' ' (p2 :: ps2)) := by
                    simpa using
                      (splitFenFieldsChars_append_sep p (joinPlacementChars ' ' (p2 :: ps2)) hp)
            _ = p :: (p2 :: ps2) := by simp [ih']

theorem splitFenFields_toFEN (gs : GameState) :
    splitFenFields (toFEN gs) =
      [ boardToFenPlacement gs.board
      , (if gs.toMove = Color.White then "w" else "b")
      , castlingToFen gs.castlingRights
      , (gs.enPassantTarget.map (fun sq => sq.algebraic) |>.getD "-")
      , toString gs.halfMoveClock
      , toString gs.fullMoveNumber
      ] := by
  unfold splitFenFields
  -- Reduce to the char-level splitter.
  have hPlacement : ' ' ∉ (boardToFenPlacement gs.board).toList :=
    boardToFenPlacement_no_space gs.board
  have hActive : ' ' ∉ (if gs.toMove = Color.White then "w" else "b").toList := by
    cases gs.toMove <;> decide
  have hCastling : ' ' ∉ (castlingToFen gs.castlingRights).toList :=
    castlingToFen_no_space gs.castlingRights
  have hEp :
      ' ' ∉ (gs.enPassantTarget.map (fun sq => sq.algebraic) |>.getD "-").toList :=
    epField_no_space gs.enPassantTarget
  have hHalf : ' ' ∉ (toString gs.halfMoveClock).toList :=
    NatString.toString_no_space gs.halfMoveClock
  have hFull : ' ' ∉ (toString gs.fullMoveNumber).toList :=
    NatString.toString_no_space gs.fullMoveNumber
  let fields : List String :=
    [ boardToFenPlacement gs.board
    , (if gs.toMove = Color.White then "w" else "b")
    , castlingToFen gs.castlingRights
    , (gs.enPassantTarget.map (fun sq => sq.algebraic) |>.getD "-")
    , toString gs.halfMoveClock
    , toString gs.fullMoveNumber
    ]
  let parts : List (List Char) := fields.map String.toList
  have hne : parts ≠ [] := by
    simp [parts, fields]
  have hNoSpace : ∀ p, p ∈ parts → ' ' ∉ p := by
    intro p hp
    have : p = (boardToFenPlacement gs.board).toList ∨
        p = (if gs.toMove = Color.White then "w" else "b").toList ∨
        p = (castlingToFen gs.castlingRights).toList ∨
        p = (gs.enPassantTarget.map (fun sq => sq.algebraic) |>.getD "-").toList ∨
        p = (toString gs.halfMoveClock).toList ∨
        p = (toString gs.fullMoveNumber).toList := by
      simpa [parts, fields] using hp
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hPlacement
    · exact hActive
    · exact hCastling
    · exact hEp
    · exact hHalf
    · exact hFull
  have hSplit : splitFenFieldsChars (joinPlacementChars ' ' parts) = parts :=
    splitFenFieldsChars_joinPlacementChars (parts := parts) hne hNoSpace
  -- `toFEN` is exactly the join with `' '` separators.
  have hToList : (toFEN gs).toList = joinPlacementChars ' ' parts := by
    unfold toFEN
    simp [fields, parts]
  -- Finish.
  -- Rewrite the input chars using `hToList`, then apply the join/split inversion theorem.
  rw [hToList]
  rw [hSplit]
  simp [fields, parts]

end Parsing
end Chess
