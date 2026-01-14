import Chess.Parsing
import Chess.BoardRoundtripProofs

namespace Chess
namespace Parsing

open Chess

theorem splitPlacementCharsAux_prefix (chars cur : List Char) (acc : List (List Char)) :
    splitPlacementCharsAux chars cur acc =
      acc.reverse ++ splitPlacementCharsAux chars cur [] := by
  induction chars generalizing cur acc with
  | nil =>
      simp [splitPlacementCharsAux]
  | cons c cs ih =>
      by_cases h : c = '/'
      · subst h
        -- Separator: commit the current segment into `acc`.
        -- LHS: commit `cur.reverse` into `acc`, then recurse.
        -- RHS: recurse with empty accumulator, then prefix by `acc.reverse`.
        have hCommit :=
          (ih (cur := []) (acc := cur.reverse :: acc))
        have hSingleton :=
          (ih (cur := []) (acc := [cur.reverse]))
        calc
          splitPlacementCharsAux ('/' :: cs) cur acc
              = splitPlacementCharsAux cs [] (cur.reverse :: acc) := by
                  simp [splitPlacementCharsAux]
          _ = (cur.reverse :: acc).reverse ++ splitPlacementCharsAux cs [] [] := by
                  simpa using hCommit
          _ = (acc.reverse ++ [cur.reverse]) ++ splitPlacementCharsAux cs [] [] := by
                  simp [List.reverse_cons, List.append_assoc]
          _ = acc.reverse ++ ([cur.reverse] ++ splitPlacementCharsAux cs [] []) := by
                  simp [List.append_assoc]
          _ = acc.reverse ++ splitPlacementCharsAux cs [] [cur.reverse] := by
                  -- `splitPlacementCharsAux cs [] [cur.reverse] = [cur.reverse] ++ splitPlacementCharsAux cs [] []`
                  -- by the induction hypothesis with singleton accumulator.
                  simpa [List.reverse_cons, List.append_assoc] using congrArg (fun t => acc.reverse ++ t) hSingleton.symm
          _ = acc.reverse ++ splitPlacementCharsAux ('/' :: cs) cur [] := by
                  simp [splitPlacementCharsAux]
      · -- Non-separator: accumulate into `cur` and apply the induction hypothesis.
        have hIH := ih (cur := c :: cur) (acc := acc)
        simpa [splitPlacementCharsAux, h] using hIH

theorem splitPlacementCharsAux_append_no_sep (xs ys : List Char) (cur : List Char) (acc : List (List Char))
    (hxs : '/' ∉ xs) :
    splitPlacementCharsAux (xs ++ ys) cur acc =
      splitPlacementCharsAux ys (xs.reverse ++ cur) acc := by
  induction xs generalizing cur acc with
  | nil =>
      simp [splitPlacementCharsAux]
  | cons c cs ih =>
      have hc : c ≠ '/' := by
        intro h
        apply hxs
        simp [h]
      have hcs : '/' ∉ cs := by
        intro hm
        apply hxs
        simp [hm]
      -- No separator in the prefix: characters are accumulated into `cur` in reverse order.
      have hIH := ih (cur := c :: cur) (acc := acc) hcs
      calc
        splitPlacementCharsAux ((c :: cs) ++ ys) cur acc
            = splitPlacementCharsAux (cs ++ ys) (c :: cur) acc := by
                simp [List.cons_append, splitPlacementCharsAux, hc]
        _ = splitPlacementCharsAux ys (cs.reverse ++ (c :: cur)) acc := by
                simpa using hIH
        _ = splitPlacementCharsAux ys ((c :: cs).reverse ++ cur) acc := by
                simp [List.reverse_cons, List.append_assoc]

theorem splitPlacementCharsAux_of_no_sep (xs cur : List Char) (hxs : '/' ∉ xs) :
    splitPlacementCharsAux xs cur [] = [(xs.reverse ++ cur).reverse] := by
  induction xs generalizing cur with
  | nil =>
      simp [splitPlacementCharsAux]
  | cons c cs ih =>
      have hc : c ≠ '/' := by
        intro h
        apply hxs
        simp [h]
      have hcs : '/' ∉ cs := by
        intro hm
        apply hxs
        simp [hm]
      simpa [splitPlacementCharsAux, hc, List.reverse_cons, List.append_assoc] using
        (ih (cur := c :: cur) hcs)

theorem splitPlacementChars_of_no_sep (xs : List Char) (hxs : '/' ∉ xs) :
    splitPlacementChars xs = [xs] := by
  simpa [splitPlacementChars] using
    (splitPlacementCharsAux_of_no_sep (xs := xs) (cur := []) hxs)

theorem splitPlacementChars_append_sep (xs ys : List Char) (hxs : '/' ∉ xs) :
    splitPlacementChars (xs ++ '/' :: ys) = xs :: splitPlacementChars ys := by
  -- Accumulate the prefix `xs` into the current segment, then split at `'/'`.
  have hMove :=
    splitPlacementCharsAux_append_no_sep (xs := xs) (ys := '/' :: ys) (cur := []) (acc := []) hxs
  have hPrefix :
      splitPlacementCharsAux (xs ++ '/' :: ys) [] [] = splitPlacementCharsAux ('/' :: ys) xs.reverse [] := by
    simpa [List.append_assoc] using hMove
  -- Commit `xs` at the separator and expose it at the head using the prefix lemma.
  have hAfter :
      splitPlacementCharsAux (xs ++ '/' :: ys) [] [] = splitPlacementCharsAux ys [] [xs] := by
    simp [splitPlacementCharsAux, hPrefix]
  calc
    splitPlacementChars (xs ++ '/' :: ys)
        = splitPlacementCharsAux (xs ++ '/' :: ys) [] [] := by rfl
    _ = splitPlacementCharsAux ys [] [xs] := by simp [hAfter]
    _ = [xs].reverse ++ splitPlacementCharsAux ys [] [] := by
          simpa using (splitPlacementCharsAux_prefix (chars := ys) (cur := []) (acc := [xs]))
    _ = xs :: splitPlacementChars ys := by rfl

theorem splitPlacementChars_joinPlacementChars (ranks : List (List Char))
    (hne : ranks ≠ []) (hNoSlash : ∀ r, r ∈ ranks → '/' ∉ r) :
    splitPlacementChars (joinPlacementChars '/' ranks) = ranks := by
  induction ranks with
  | nil =>
      cases hne rfl
  | cons r rs ih =>
      cases rs with
      | nil =>
          have hr : '/' ∉ r := hNoSlash r (by simp)
          simp [joinPlacementChars, splitPlacementChars_of_no_sep r hr]
      | cons r2 rs2 =>
          have hr : '/' ∉ r := hNoSlash r (by simp)
          have hne' : (r2 :: rs2) ≠ [] := by simp
          have hNoSlash' : ∀ r, r ∈ (r2 :: rs2) → '/' ∉ r := by
            intro r' hr'
            exact hNoSlash r' (by simp [hr'])
          have ih' : splitPlacementChars (joinPlacementChars '/' (r2 :: rs2)) = (r2 :: rs2) :=
            ih hne' hNoSlash'
          calc
            splitPlacementChars (joinPlacementChars '/' (r :: r2 :: rs2))
                = splitPlacementChars (r ++ '/' :: joinPlacementChars '/' (r2 :: rs2)) := by
                    simp [joinPlacementChars]
            _ = r :: splitPlacementChars (joinPlacementChars '/' (r2 :: rs2)) := by
                    simpa using
                      (splitPlacementChars_append_sep r (joinPlacementChars '/' (r2 :: rs2)) hr)
            _ = r :: (r2 :: rs2) := by simp [ih']

end Parsing
end Chess
