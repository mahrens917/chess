import Chess.Parsing
import Chess.Rules

-- Define List.All at top level so it truly extends the List namespace
-- and field notation l.All works correctly
section ListLemmas

/-- Propositional version of List.all: All elements satisfy the predicate -/
def List.All {α : Type _} : List α → (α → Prop) → Prop
  | [], _ => True
  | a :: as, p => p a ∧ List.All as p

theorem List.All.mem {α : Type _} {p : α → Prop} :
    ∀ {l : List α}, l.All p → ∀ {a}, a ∈ l → p a
  | [], _, _, h => by cases h
  | _ :: l, hall, b, hmem => by
      rcases hall with ⟨ha, hall⟩
      rcases List.mem_cons.mp hmem with h | h
      · cases h
        simpa using ha
      · exact List.All.mem hall h

theorem List.All.head {α : Type _} {p : α → Prop} {l : List α}
    (hall : l.All p) (hne : l ≠ []) :
    p (l.head hne) :=
  List.All.mem hall (List.head_mem hne)

theorem List.All.getLast {α : Type _} {p : α → Prop} {l : List α}
    (hall : l.All p) (hne : l ≠ []) :
    p (l.getLast hne) :=
  List.All.mem hall (List.getLast_mem hne)

end ListLemmas

namespace Chess
namespace Parsing

open Rules
open scoped Classical

theorem String.front_ofList_cons (c : Char) (cs : List Char) :
    (String.ofList (c :: cs)).front = c := by
  simp only [String.front, String.Pos.Raw.get, String.toList_ofList]
  unfold String.Pos.Raw.utf8GetAux
  simp

theorem String.front_eq_head {s : String} (hne : s ≠ "")
    (hlist : s.toList ≠ []) :
    s.front = s.toList.head hlist := by
  classical
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  cases l with
  | nil =>
      cases hlist rfl
  | cons c cs =>
      simp [String.front_ofList_cons]

-- TODO: String internal API has changed in Lean 4 - needs rewrite
theorem String.back_ofList_cons (c : Char) (cs : List Char) :
    (String.ofList (c :: cs)).back =
      (match cs with
       | [] => c
       | _ => (String.ofList cs).back) := by
  sorry

-- TODO: String internal API has changed in Lean 4 - needs rewrite
theorem String.back_eq_getLast {s : String} (hne : s ≠ "")
    (hlist : s.toList ≠ []) :
    s.back = s.toList.getLast
      (by
        intro hnil
        exact hne ((String.toList_eq_nil_iff).1 hnil)) := by
  sorry

-- TODO: String internal API has changed in Lean 4 - needs rewrite
theorem trim_eq_self_of_nonWhitespace_ends (s : String)
    (hne : s ≠ "")
    (hfront : s.front.isWhitespace = false)
    (hback : s.back.isWhitespace = false) :
    s.trim = s := by
  sorry

-- TODO: depends on String proofs that need updating for Lean 4
theorem repr_trim (n : Nat) : (Nat.repr n).trim = Nat.repr n := by
  sorry

section NatDecimalLemmas

open Nat

private theorem digitChar_isDigit (n : Nat) (h : n < 10) :
    (Nat.digitChar n).isDigit = true := by
  match n, h with
  | 0, _ => native_decide
  | 1, _ => native_decide
  | 2, _ => native_decide
  | 3, _ => native_decide
  | 4, _ => native_decide
  | 5, _ => native_decide
  | 6, _ => native_decide
  | 7, _ => native_decide
  | 8, _ => native_decide
  | 9, _ => native_decide
  | n + 10, h => omega

private theorem digitChar_value (n : Nat) (h : n < 10) :
    (Nat.digitChar n).toNat - '0'.toNat = n := by
  match n, h with
  | 0, _ => native_decide
  | 1, _ => native_decide
  | 2, _ => native_decide
  | 3, _ => native_decide
  | 4, _ => native_decide
  | 5, _ => native_decide
  | 6, _ => native_decide
  | 7, _ => native_decide
  | 8, _ => native_decide
  | 9, _ => native_decide
  | n + 10, h => omega

private def digitValue (c : Char) : Nat :=
  c.toNat - '0'.toNat

private theorem digitValue_digitChar (n : Nat) (h : n < 10) :
    digitValue (Nat.digitChar n) = n := by
  unfold digitValue
  exact digitChar_value n h

private theorem digitChar_notWhitespace (n : Nat) (h : n < 10) :
    (Nat.digitChar n).isWhitespace = false := by
  match n, h with
  | 0, _ => native_decide
  | 1, _ => native_decide
  | 2, _ => native_decide
  | 3, _ => native_decide
  | 4, _ => native_decide
  | 5, _ => native_decide
  | 6, _ => native_decide
  | 7, _ => native_decide
  | 8, _ => native_decide
  | 9, _ => native_decide
  | n + 10, h => omega

private theorem digitValue_nonneg (c : Char) : digitValue c ≤ c.toNat := by
  unfold digitValue
  exact Nat.sub_le _ _

private def decodeDigits (digits : List Char) : Nat :=
  digits.foldl (fun acc c => acc * 10 + digitValue c) 0

-- Generalized version with arbitrary initial accumulator
private theorem decodeDigits_foldl_append (init : Nat) (xs : List Char) (c : Char) :
    List.foldl (fun acc c => acc * 10 + digitValue c) init (xs ++ [c]) =
    List.foldl (fun acc c => acc * 10 + digitValue c) init xs * 10 + digitValue c := by
  induction xs generalizing init with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.cons_append, List.foldl_cons]
      exact ih _

private theorem decodeDigits_append_snoc (xs : List Char) (c : Char) :
    decodeDigits (xs ++ [c]) = decodeDigits xs * 10 + digitValue c := by
  unfold decodeDigits
  exact decodeDigits_foldl_append 0 xs c

private theorem toDigitsCore_all_digits
    (fuel n : Nat) (acc : List Char) :
    acc.All (fun c => c.isDigit = true) →
    (Nat.toDigitsCore 10 fuel n acc).All (fun c => c.isDigit = true) := by
  induction fuel generalizing n acc with
  | zero =>
    intro h
    simp only [Nat.toDigitsCore]
    exact h
  | succ fuel ih =>
    intro h
    simp only [Nat.toDigitsCore]
    split
    · have digit_is_digit : (Nat.digitChar (n % 10)).isDigit = true := by
        apply digitChar_isDigit
        exact Nat.mod_lt n (by decide)
      exact ⟨digit_is_digit, h⟩
    · have digit_is_digit : (Nat.digitChar (n % 10)).isDigit = true := by
        apply digitChar_isDigit
        exact Nat.mod_lt n (by decide)
      apply ih
      exact ⟨digit_is_digit, h⟩

private theorem toDigitsCore_no_whitespace
    (fuel n : Nat) (acc : List Char) :
    acc.All (fun c => c.isWhitespace = false) →
    (Nat.toDigitsCore 10 fuel n acc).All (fun c => c.isWhitespace = false) := by
  induction fuel generalizing n acc with
  | zero =>
    intro h
    simp only [Nat.toDigitsCore]
    exact h
  | succ fuel ih =>
    intro h
    simp only [Nat.toDigitsCore]
    split
    · have digit_no_ws : (Nat.digitChar (n % 10)).isWhitespace = false := by
        apply digitChar_notWhitespace
        exact Nat.mod_lt n (by decide)
      exact ⟨digit_no_ws, h⟩
    · have digit_no_ws : (Nat.digitChar (n % 10)).isWhitespace = false := by
        apply digitChar_notWhitespace
        exact Nat.mod_lt n (by decide)
      apply ih
      exact ⟨digit_no_ws, h⟩

private theorem toDigitsCore_append (base fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore base fuel n acc =
      Nat.toDigitsCore base fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero =>
    simp only [Nat.toDigitsCore, List.nil_append]
  | succ fuel ih =>
    simp only [Nat.toDigitsCore]
    split
    · simp only [List.cons_append, List.nil_append]
    · rw [ih, ih (acc := [(Nat.digitChar (n % base))])]
      simp only [List.cons_append, List.nil_append, List.append_assoc]

private theorem div_ten_lt_self {n : Nat} (h : 0 < n) : n / 10 < n := by
  simpa using (Nat.div_lt_self h (show 1 < 10 by decide))

private theorem mod_ten_lt_ten (n : Nat) : n % 10 < 10 :=
  Nat.mod_lt _ (by decide : 0 < 10)

private theorem toDigits_all_digits (n : Nat) :
    (Nat.toDigits 10 n).All (fun c => c.isDigit = true) := by
  unfold Nat.toDigits
  apply toDigitsCore_all_digits
  trivial

private theorem toDigits_no_whitespace (n : Nat) :
    (Nat.toDigits 10 n).All (fun c => c.isWhitespace = false) := by
  unfold Nat.toDigits
  apply toDigitsCore_no_whitespace
  trivial

private theorem toDigitsCore_ne_nil (fuel n : Nat) (acc : List Char) (hacc : acc ≠ []) :
    Nat.toDigitsCore 10 fuel n acc ≠ [] := by
  rw [toDigitsCore_append]
  intro h
  rw [List.append_eq_nil_iff] at h
  exact hacc h.2

private theorem toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  unfold Nat.toDigits
  simp only [Nat.toDigitsCore]
  split
  · simp only [ne_eq, List.cons_ne_self, not_false_eq_true]
  · apply toDigitsCore_ne_nil
    simp only [ne_eq, List.cons_ne_self, not_false_eq_true]

private theorem decodeDigits_toDigitsCore
    {fuel n : Nat} (hfuel : fuel ≥ n + 1) :
    decodeDigits (Nat.toDigitsCore 10 fuel n []) = n := by
  match fuel with
  | 0 => omega
  | fuel' + 1 =>
    simp only [Nat.toDigitsCore]
    split
    · -- q = n / 10 = 0, so n < 10
      rename_i hq
      simp only [decodeDigits, List.foldl_cons, List.foldl_nil]
      simp only [digitValue_digitChar (n % 10) (Nat.mod_lt n (by decide))]
      have : n < 10 := by omega
      omega
    · -- q = n / 10 ≠ 0
      rename_i hq
      rw [toDigitsCore_append]
      rw [decodeDigits_append_snoc]
      have hq_lt : n / 10 < n := Nat.div_lt_self (by omega) (by decide)
      have hfuel_q : fuel' ≥ n / 10 + 1 := by omega
      have ih := decodeDigits_toDigitsCore (fuel := fuel') (n := n / 10) hfuel_q
      rw [ih]
      simp only [digitValue_digitChar (n % 10) (Nat.mod_lt n (by decide))]
      omega
termination_by n
decreasing_by
  simp_wf
  exact hq_lt

private theorem decodeDigits_toDigits (n : Nat) :
    decodeDigits (Nat.toDigits 10 n) = n := by
  simpa [Nat.toDigits] using
    decodeDigits_toDigitsCore (fuel := n + 1) (n := n) (by simp)

private theorem repr_toDigits_list (n : Nat) :
    (Nat.repr n).toList = Nat.toDigits 10 n := by
  simp [Nat.repr]

private theorem repr_nonempty (n : Nat) : (Nat.repr n).isEmpty = false := by
  have hdigits := toDigits_ne_nil n
  have hrepr_ne : Nat.repr n ≠ "" := by
    intro hrepr
    have : Nat.toDigits 10 n = [] := by
      simpa [repr_toDigits_list] using congrArg String.toList hrepr
    exact hdigits this
  have hsize : (Nat.repr n).utf8ByteSize = 0 → False := by
    intro hzero
    have : Nat.repr n = "" := (String.utf8ByteSize_eq_zero_iff.mp hzero)
    exact hrepr_ne this
  have hzero :
      ((Nat.repr n).utf8ByteSize == 0) = false :=
    (decide_eq_false_iff_not).2 (by
      intro h
      exact hsize h)
  simpa [String.isEmpty] using hzero

private theorem repr_list_all_digits (n : Nat) :
    (Nat.repr n).toList.All (fun c => c.isDigit = true) := by
  simpa [repr_toDigits_list] using toDigits_all_digits n

private theorem repr_list_no_whitespace (n : Nat) :
    (Nat.repr n).toList.All (fun c => c.isWhitespace = false) := by
  simpa [repr_toDigits_list] using toDigits_no_whitespace n

-- TODO: String internal API has changed - needs rewrite
theorem String.foldl_ofList {α : Type _} (f : α → Char → α) (init : α) :
    ∀ l : List Char, String.foldl f init (String.ofList l) = List.foldl f init l := by
  sorry

-- TODO: String internal API has changed - needs rewrite
theorem String.all_ofList (p : Char → Bool) :
    ∀ l : List Char, (String.ofList l).all p = l.all p := by
  sorry

theorem repr_eq_ofList (n : Nat) :
    Nat.repr n = String.ofList (Nat.toDigits 10 n) := by
  apply String.toList_injective
  simp [repr_toDigits_list]

theorem repr_isNat (n : Nat) :
    (Nat.repr n).isNat = true := by
  have hallDigits :
      (Nat.toDigits 10 n).All (fun c => c.isDigit = true) := by
    simpa [repr_toDigits_list] using repr_list_all_digits n
  have hbool : (Nat.toDigits 10 n).all Char.isDigit = true := by
    refine List.all_eq_true.mpr ?_
    intro c hc
    have : c.isDigit = true := List.All.mem hallDigits hc
    simpa using this
  have hrepr := repr_eq_ofList n
  have hallStr :
      (Nat.repr n).all Char.isDigit = true := by
    simpa [hrepr, String.all_ofList] using hbool
  have hnonempty : (Nat.repr n).isEmpty = false := repr_nonempty n
  simp [String.isNat, hnonempty, hallStr]

-- TODO: depends on String.foldl_ofList which uses sorry
theorem toNat?_repr (n : Nat) : String.toNat? (Nat.repr n) = some n := by
  sorry

end NatDecimalLemmas

theorem List.find?_eq_some_of_exists {α : Type _} {p : α → Prop} [DecidablePred p]
    {l : List α} :
    (∃ x ∈ l, p x) → ∃ y, l.find? p = some y := by
  induction l with
  | nil =>
      intro h
      rcases h with ⟨x, hx, _⟩
      cases hx
  | cons a rest ih =>
      intro h
      by_cases hpa : p a
      · exact ⟨a, by simp [List.find?, hpa]⟩
      · rcases h with ⟨x, hxmem, hpx⟩
        have hxrest : ∃ x ∈ rest, p x := by
          have hxmem' := List.mem_cons.mp hxmem
          have hxmemTail : x ∈ rest := by
            cases hxmem' with
            | inl hx =>
                subst hx
                exact (hpa hpx).elim
            | inr htail => exact htail
          exact ⟨x, hxmemTail, hpx⟩
        obtain ⟨y, hy⟩ := ih hxrest
        exact ⟨y, by simp [List.find?, hpa, hy]⟩

-- TODO: Proof needs update for current API (do-notation in theorem type causes issues)
-- theorem applyLegalMoves_cons (gs : GameState) (m : Move) (rest : List Move) :
--     Rules.applyLegalMoves gs (m :: rest) = do
--       let next ← Rules.applyLegalMove gs m
--       Rules.applyLegalMoves next rest := by sorry

theorem Except.exists_ok_of_bind_ok {ε α β : Type _}
    {f : Except ε α} {g : α → Except ε β} {b : β}
    (h : f.bind g = Except.ok b) :
    ∃ a, f = Except.ok a ∧ g a = Except.ok b := by
  cases f with
  | error _ =>
      simp [Except.bind] at h
  | ok a =>
      refine ⟨a, rfl, ?_⟩
      simpa [Except.bind] using h

-- TODO: The following theorems reference functions (PGNScaffold, assemblePGNGame,
-- buildPGNScaffold, reconcileFinalState, etc.) that have been removed from the codebase.
-- These proofs need to be rewritten once the new parsing architecture is stabilized.

end Parsing
end Chess
