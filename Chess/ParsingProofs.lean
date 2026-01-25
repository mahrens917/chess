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

-- ============================================================================
-- String.foldl / String.all proofs via byte-position iteration
-- ============================================================================

section StringFoldlProofs

-- Sum of UTF-8 byte sizes for a character list
private def utf8SizeSum : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + utf8SizeSum cs

private theorem utf8SizeSum_append (l1 l2 : List Char) :
    utf8SizeSum (l1 ++ l2) = utf8SizeSum l1 + utf8SizeSum l2 := by
  induction l1 with
  | nil => simp [utf8SizeSum]
  | cons c cs ih => simp [utf8SizeSum, ih]; omega

-- One-step unfolding lemmas for foldlAux/anyAux
private theorem foldlAux_step {α : Type _} (f : α → Char → α) (s : String)
    (stop pos : String.Pos.Raw) (a : α) (h : pos < stop) :
    String.foldlAux f s stop pos a =
      String.foldlAux f s stop (pos.next s) (f a (pos.get s)) := by
  rw [String.foldlAux.eq_1, dif_pos h]

private theorem foldlAux_done {α : Type _} (f : α → Char → α) (s : String)
    (stop pos : String.Pos.Raw) (a : α) (h : ¬ pos < stop) :
    String.foldlAux f s stop pos a = a := by
  rw [String.foldlAux.eq_1, dif_neg h]

private theorem anyAux_step (s : String) (stop : String.Pos.Raw) (p : Char → Bool)
    (pos : String.Pos.Raw) (h : pos < stop) (hp : p (pos.get s) = false) :
    String.anyAux s stop p pos = String.anyAux s stop p (pos.next s) := by
  rw [String.anyAux.eq_1, dif_pos h, if_neg (by simp [hp])]

private theorem anyAux_step_true (s : String) (stop : String.Pos.Raw) (p : Char → Bool)
    (pos : String.Pos.Raw) (h : pos < stop) (hp : p (pos.get s) = true) :
    String.anyAux s stop p pos = true := by
  rw [String.anyAux.eq_1, dif_pos h, if_pos (by simp [hp])]

private theorem anyAux_done (s : String) (stop : String.Pos.Raw) (p : Char → Bool)
    (pos : String.Pos.Raw) (h : ¬ pos < stop) :
    String.anyAux s stop p pos = false := by
  rw [String.anyAux.eq_1, dif_neg h]

-- Key lemma: utf8GetAux returns the right character at accumulated byte position
private theorem utf8GetAux_at_sum (pref : List Char) (c : Char) (suf : List Char)
    (startPos : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (pref ++ c :: suf) startPos
      (⟨startPos.byteIdx + utf8SizeSum pref⟩ : String.Pos.Raw) = c := by
  induction pref generalizing startPos with
  | nil =>
    simp [utf8SizeSum]
    unfold String.Pos.Raw.utf8GetAux
    rw [if_pos (String.Pos.Raw.ext rfl).symm]
  | cons p ps ih =>
    simp only [List.cons_append]
    unfold String.Pos.Raw.utf8GetAux
    have hne : startPos ≠
        (⟨startPos.byteIdx + utf8SizeSum (p :: ps)⟩ : String.Pos.Raw) := by
      intro h
      have := congrArg String.Pos.Raw.byteIdx h
      simp [utf8SizeSum] at this
      have : p.utf8Size > 0 := Char.utf8Size_pos p
      omega
    rw [if_neg hne,
      show (⟨startPos.byteIdx + utf8SizeSum (p :: ps)⟩ : String.Pos.Raw) =
        (⟨(startPos + p).byteIdx + utf8SizeSum ps⟩ : String.Pos.Raw) from
        String.Pos.Raw.ext (by
          simp [String.Pos.Raw.byteIdx_add_char, utf8SizeSum]; omega)]
    exact ih (startPos + p)

-- utf8ByteSize of String.ofList equals utf8SizeSum
private theorem utf8ByteSize_eq_utf8SizeSum (l : List Char) :
    (String.ofList l).utf8ByteSize = utf8SizeSum l := by
  induction l with
  | nil => simp [String.ofList_nil, utf8SizeSum]
  | cons c cs ih =>
    have : String.ofList (c :: cs) = String.singleton c ++ String.ofList cs := by
      rw [show c :: cs = [c] ++ cs from rfl, String.ofList_append, String.singleton_eq_ofList]
    rw [this, String.utf8ByteSize_append, String.utf8ByteSize_singleton, utf8SizeSum, ih]

private theorem utf8SizeSum_lt_append_cons (pref : List Char) (c : Char) (cs : List Char) :
    utf8SizeSum pref < utf8SizeSum (pref ++ c :: cs) := by
  rw [utf8SizeSum_append]; simp [utf8SizeSum]
  have : c.utf8Size > 0 := Char.utf8Size_pos c; omega

-- get/next at byte offset of prefix yields the next character
private theorem get_at_prefix_end (pref : List Char) (c : Char) (suf : List Char) :
    (⟨utf8SizeSum pref⟩ : String.Pos.Raw).get (String.ofList (pref ++ c :: suf)) = c := by
  show String.Pos.Raw.get (String.ofList (pref ++ c :: suf)) ⟨utf8SizeSum pref⟩ = c
  simp only [String.Pos.Raw.get, String.toList_ofList]
  have h : (⟨utf8SizeSum pref⟩ : String.Pos.Raw) =
      (⟨(0 : String.Pos.Raw).byteIdx + utf8SizeSum pref⟩ : String.Pos.Raw) := by
    simp [String.Pos.Raw.byteIdx_zero]
  rw [h]
  exact utf8GetAux_at_sum pref c suf 0

private theorem next_at_prefix_end (pref : List Char) (c : Char) (suf : List Char) :
    (⟨utf8SizeSum pref⟩ : String.Pos.Raw).next (String.ofList (pref ++ c :: suf)) =
      (⟨utf8SizeSum (pref ++ [c])⟩ : String.Pos.Raw) := by
  show String.Pos.Raw.next (String.ofList (pref ++ c :: suf)) ⟨utf8SizeSum pref⟩ =
    ⟨utf8SizeSum (pref ++ [c])⟩
  simp only [String.Pos.Raw.next, get_at_prefix_end]
  exact String.Pos.Raw.ext (by
    simp [String.Pos.Raw.byteIdx_add_char, utf8SizeSum_append, utf8SizeSum])

-- General foldlAux lemma: starting at byte offset of prefix visits suffix chars
private theorem foldlAux_suffix {α : Type _} (f : α → Char → α)
    (pref suf : List Char) (a : α) :
    String.foldlAux f (String.ofList (pref ++ suf))
      (String.ofList (pref ++ suf)).rawEndPos
      (⟨utf8SizeSum pref⟩ : String.Pos.Raw) a = suf.foldl f a := by
  induction suf generalizing pref a with
  | nil =>
    simp only [List.append_nil]
    exact foldlAux_done _ _ _ _ _ (by
      simp [String.rawEndPos, String.Pos.Raw.lt_iff, utf8ByteSize_eq_utf8SizeSum])
  | cons c cs ih =>
    have h_lt : (⟨utf8SizeSum pref⟩ : String.Pos.Raw) <
        (String.ofList (pref ++ c :: cs)).rawEndPos := by
      simp only [String.rawEndPos, String.Pos.Raw.lt_iff, utf8ByteSize_eq_utf8SizeSum]
      exact utf8SizeSum_lt_append_cons pref c cs
    rw [foldlAux_step _ _ _ _ _ h_lt, get_at_prefix_end, next_at_prefix_end]
    simp only [List.foldl_cons]
    rw [show String.ofList (pref ++ c :: cs) = String.ofList ((pref ++ [c]) ++ cs) from by
      congr 1; simp [List.append_assoc]]
    exact ih (pref ++ [c]) (f a c)

-- General anyAux lemma: starting at byte offset of prefix checks suffix chars
private theorem anyAux_suffix (p : Char → Bool) (pref suf : List Char) :
    String.anyAux (String.ofList (pref ++ suf))
      (String.ofList (pref ++ suf)).rawEndPos p
      (⟨utf8SizeSum pref⟩ : String.Pos.Raw) = suf.any p := by
  induction suf generalizing pref with
  | nil =>
    simp only [List.append_nil, List.any_nil]
    exact anyAux_done _ _ _ _ (by
      simp [String.rawEndPos, String.Pos.Raw.lt_iff, utf8ByteSize_eq_utf8SizeSum])
  | cons c cs ih =>
    have h_lt : (⟨utf8SizeSum pref⟩ : String.Pos.Raw) <
        (String.ofList (pref ++ c :: cs)).rawEndPos := by
      simp only [String.rawEndPos, String.Pos.Raw.lt_iff, utf8ByteSize_eq_utf8SizeSum]
      exact utf8SizeSum_lt_append_cons pref c cs
    simp only [List.any_cons]
    cases hp : p c with
    | true =>
      rw [anyAux_step_true _ _ _ _ h_lt (by rw [get_at_prefix_end]; exact hp)]
      simp
    | false =>
      rw [anyAux_step _ _ _ _ h_lt (by
            show p ((⟨utf8SizeSum pref⟩ : String.Pos.Raw).get
              (String.ofList (pref ++ c :: cs))) = false
            rw [get_at_prefix_end]; exact hp),
          next_at_prefix_end]
      simp only [Bool.false_or]
      rw [show String.ofList (pref ++ c :: cs) = String.ofList ((pref ++ [c]) ++ cs) from by
        congr 1; simp [List.append_assoc]]
      exact ih (pref ++ [c])

-- ============================================================================
-- String.back / String.trim proofs via byte-position iteration
-- ============================================================================

-- Key lemma: utf8PrevAux at the end of a non-empty list returns position of last char
private theorem utf8PrevAux_at_end (pref : List Char) (c : Char)
    (startPos : String.Pos.Raw) :
    String.Pos.Raw.utf8PrevAux (pref ++ [c]) startPos
      (⟨startPos.byteIdx + utf8SizeSum (pref ++ [c])⟩ : String.Pos.Raw) =
      (⟨startPos.byteIdx + utf8SizeSum pref⟩ : String.Pos.Raw) := by
  induction pref generalizing startPos with
  | nil =>
    simp [utf8SizeSum]
    unfold String.Pos.Raw.utf8PrevAux
    have h_le : (⟨startPos.byteIdx + c.utf8Size⟩ : String.Pos.Raw) ≤ (startPos + c) := by
      simp [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_add_char]
    rw [if_pos h_le]
  | cons d ds ih =>
    simp only [List.cons_append]
    unfold String.Pos.Raw.utf8PrevAux
    have h_not_le : ¬ ((⟨startPos.byteIdx + utf8SizeSum (d :: (ds ++ [c]))⟩ : String.Pos.Raw) ≤
        (startPos + d)) := by
      simp [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_add_char, utf8SizeSum, utf8SizeSum_append]
      have : c.utf8Size > 0 := Char.utf8Size_pos c
      omega
    rw [if_neg h_not_le]
    have h_target : (⟨startPos.byteIdx + utf8SizeSum (d :: (ds ++ [c]))⟩ : String.Pos.Raw) =
        (⟨(startPos + d).byteIdx + utf8SizeSum (ds ++ [c])⟩ : String.Pos.Raw) := by
      apply String.Pos.Raw.ext
      simp [String.Pos.Raw.byteIdx_add_char, utf8SizeSum]
      omega
    rw [h_target, ih (startPos + d)]
    apply String.Pos.Raw.ext
    simp [String.Pos.Raw.byteIdx_add_char, utf8SizeSum]
    omega

-- Helper: non-empty string has positive utf8ByteSize
private theorem utf8ByteSize_pos_of_ne_empty {s : String} (hne : s ≠ "") :
    0 < s.utf8ByteSize := by
  have h_toList_ne : s.toList ≠ [] := by
    intro h; exact hne (String.toList_eq_nil_iff.1 h)
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil h_toList_ne
  rw [show s.utf8ByteSize = (String.ofList s.toList).utf8ByteSize from by
    rw [@String.ofList_toList s]]
  rw [utf8ByteSize_eq_utf8SizeSum, hcs, utf8SizeSum]
  have : c.utf8Size > 0 := Char.utf8Size_pos c
  omega

-- back of ofList equals getLast
private theorem back_ofList_eq_getLast (l : List Char) (hne : l ≠ []) :
    (String.ofList l).back = l.getLast hne := by
  show String.Pos.Raw.get (String.ofList l)
    (String.Pos.Raw.utf8PrevAux (String.ofList l).toList 0 (String.ofList l).rawEndPos) =
    l.getLast hne
  rw [String.toList_ofList]
  have h_endPos : (String.ofList l).rawEndPos = (⟨utf8SizeSum l⟩ : String.Pos.Raw) := by
    simp [String.rawEndPos, utf8ByteSize_eq_utf8SizeSum]
  rw [h_endPos]
  have h_prev : String.Pos.Raw.utf8PrevAux l 0 (⟨utf8SizeSum l⟩ : String.Pos.Raw) =
      (⟨utf8SizeSum l.dropLast⟩ : String.Pos.Raw) := by
    have h_split : l = l.dropLast ++ [l.getLast hne] :=
      (List.dropLast_concat_getLast hne).symm
    suffices h : String.Pos.Raw.utf8PrevAux (l.dropLast ++ [l.getLast hne]) 0
        (⟨utf8SizeSum (l.dropLast ++ [l.getLast hne])⟩ : String.Pos.Raw) =
        (⟨utf8SizeSum l.dropLast⟩ : String.Pos.Raw) by
      rwa [← h_split] at h
    rw [show (⟨utf8SizeSum (l.dropLast ++ [l.getLast hne])⟩ : String.Pos.Raw) =
        (⟨(0 : String.Pos.Raw).byteIdx + utf8SizeSum (l.dropLast ++ [l.getLast hne])⟩ :
          String.Pos.Raw) from by
      simp [String.Pos.Raw.byteIdx_zero]]
    rw [utf8PrevAux_at_end l.dropLast (l.getLast hne) 0]
    simp [String.Pos.Raw.byteIdx_zero]
  rw [h_prev]
  have h_split : l = l.dropLast ++ [l.getLast hne] :=
    (List.dropLast_concat_getLast hne).symm
  rw [show String.ofList l = String.ofList (l.dropLast ++ l.getLast hne :: []) from
    congrArg String.ofList h_split]
  exact get_at_prefix_end l.dropLast (l.getLast hne) []

-- go₂ on a full list returns the list itself
private theorem extract_go₂_full (l : List Char) (startPos : String.Pos.Raw) :
    String.Pos.Raw.extract.go₂ l startPos
      (⟨startPos.byteIdx + utf8SizeSum l⟩ : String.Pos.Raw) = l := by
  induction l generalizing startPos with
  | nil => simp [utf8SizeSum]; rfl
  | cons c cs ih =>
    rw [String.Pos.Raw.extract.go₂.eq_2]
    have hne : startPos ≠ (⟨startPos.byteIdx + utf8SizeSum (c :: cs)⟩ : String.Pos.Raw) := by
      intro h
      have := congrArg String.Pos.Raw.byteIdx h
      simp [utf8SizeSum] at this
      have : c.utf8Size > 0 := Char.utf8Size_pos c
      omega
    rw [if_neg hne]
    congr 1
    rw [show (⟨startPos.byteIdx + utf8SizeSum (c :: cs)⟩ : String.Pos.Raw) =
        (⟨(startPos + c).byteIdx + utf8SizeSum cs⟩ : String.Pos.Raw) from
      String.Pos.Raw.ext (by
        simp [String.Pos.Raw.byteIdx_add_char, utf8SizeSum]; omega)]
    exact ih (startPos + c)

-- extract from 0 to rawEndPos = identity
private theorem extract_zero_rawEndPos (s : String) (hne : s ≠ "") :
    String.Pos.Raw.extract s 0 s.rawEndPos = s := by
  show (if (0 : String.Pos.Raw).byteIdx ≥ s.rawEndPos.byteIdx then ""
    else String.ofList (String.Pos.Raw.extract.go₁ s.toList 0 0 s.rawEndPos)) = s
  have h_not_ge : ¬ ((0 : String.Pos.Raw).byteIdx ≥ s.rawEndPos.byteIdx) := by
    show ¬ (0 ≥ s.utf8ByteSize)
    have := utf8ByteSize_pos_of_ne_empty hne
    omega
  rw [if_neg h_not_ge]
  have h_toList_ne : s.toList ≠ [] := by
    intro h; exact hne (String.toList_eq_nil_iff.1 h)
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil h_toList_ne
  rw [hcs, String.Pos.Raw.extract.go₁.eq_2]
  simp only [ite_true]
  have h_endPos : s.rawEndPos = (⟨utf8SizeSum s.toList⟩ : String.Pos.Raw) := by
    apply String.Pos.Raw.ext
    show s.utf8ByteSize = utf8SizeSum s.toList
    have h := utf8ByteSize_eq_utf8SizeSum s.toList
    rw [show String.ofList s.toList = s from String.ofList_toList] at h
    exact h
  rw [h_endPos, hcs]
  rw [show (⟨utf8SizeSum (c :: cs)⟩ : String.Pos.Raw) =
      (⟨(0 : String.Pos.Raw).byteIdx + utf8SizeSum (c :: cs)⟩ : String.Pos.Raw) from by
    apply String.Pos.Raw.ext; simp]
  rw [extract_go₂_full (c :: cs) 0, ← hcs]
  exact @String.ofList_toList s

-- takeWhileAux stops immediately if first char doesn't satisfy predicate
private theorem takeWhileAux_stop_first_false (s : String) (hne : s ≠ "")
    (p : Char → Bool) (hp : p s.front = false) :
    Substring.Raw.takeWhileAux s s.rawEndPos p 0 = 0 := by
  rw [Substring.Raw.takeWhileAux.eq_1]
  have h_lt : (0 : String.Pos.Raw) < s.rawEndPos := by
    simp only [String.Pos.Raw.lt_iff, String.rawEndPos]
    exact utf8ByteSize_pos_of_ne_empty hne
  rw [dif_pos h_lt]
  have h_not : ¬ (p (String.Pos.Raw.get s 0) = true) := by
    rw [show String.Pos.Raw.get s 0 = s.front from rfl, hp]
    exact Bool.false_ne_true
  exact if_neg h_not

-- takeRightWhileAux stops if last char doesn't satisfy predicate
private theorem takeRightWhileAux_stop_last_false (s : String) (hne : s ≠ "")
    (p : Char → Bool) (hp : p s.back = false) :
    Substring.Raw.takeRightWhileAux s 0 p s.rawEndPos = s.rawEndPos := by
  rw [Substring.Raw.takeRightWhileAux.eq_def]
  have h_lt : (0 : String.Pos.Raw) < s.rawEndPos := by
    simp only [String.Pos.Raw.lt_iff, String.rawEndPos]
    exact utf8ByteSize_pos_of_ne_empty hne
  rw [dif_pos h_lt]
  have h_true : (! p (String.Pos.Raw.get s (String.Pos.Raw.prev s s.rawEndPos))) = true := by
    show (! p s.back) = true
    rw [hp]; simp
  exact if_pos h_true

end StringFoldlProofs

theorem String.back_ofList_cons (c : Char) (cs : List Char) :
    (String.ofList (c :: cs)).back =
      (match cs with
       | [] => c
       | _ => (String.ofList cs).back) := by
  cases cs with
  | nil =>
    have h := back_ofList_eq_getLast [c] (List.cons_ne_nil c [])
    simp [List.getLast_singleton] at h
    exact h
  | cons d ds =>
    simp only
    have h1 := back_ofList_eq_getLast (c :: d :: ds) (List.cons_ne_nil c (d :: ds))
    have h2 := back_ofList_eq_getLast (d :: ds) (List.cons_ne_nil d ds)
    rw [h1, h2]
    exact List.getLast_cons (List.cons_ne_nil d ds)

theorem String.back_eq_getLast {s : String} (hne : s ≠ "")
    (hlist : s.toList ≠ []) :
    s.back = s.toList.getLast
      (by intro hnil; exact hne ((String.toList_eq_nil_iff).1 hnil)) := by
  have h := back_ofList_eq_getLast s.toList hlist
  rw [String.ofList_toList] at h
  exact h

theorem trim_eq_self_of_nonWhitespace_ends (s : String)
    (hne : s ≠ "")
    (hfront : s.front.isWhitespace = false)
    (hback : s.back.isWhitespace = false) :
    s.trim = s := by
  have h1 : Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace 0 = 0 :=
    takeWhileAux_stop_first_false s hne Char.isWhitespace hfront
  have h2 : Substring.Raw.takeRightWhileAux s 0 Char.isWhitespace s.rawEndPos = s.rawEndPos :=
    takeRightWhileAux_stop_last_false s hne Char.isWhitespace hback
  show Substring.Raw.toString (Substring.Raw.trim (String.toRawSubstring s)) = s
  simp only [String.toRawSubstring, Substring.Raw.trim]
  show String.Pos.Raw.extract s
    (Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace 0)
    (Substring.Raw.takeRightWhileAux s
      (Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace 0)
      Char.isWhitespace s.rawEndPos) = s
  rw [h1, h2]
  exact extract_zero_rawEndPos s hne

theorem repr_trim (n : Nat) : (Nat.repr n).trim = Nat.repr n := by
  have hne : Nat.repr n ≠ "" := by
    intro h; have := repr_nonempty n; simp [h, String.isEmpty] at this
  have hlist : (Nat.repr n).toList ≠ [] := by
    intro h; exact hne (String.toList_eq_nil_iff.1 h)
  have h_no_ws := repr_list_no_whitespace n
  have hfront : (Nat.repr n).front.isWhitespace = false := by
    have h_head := String.front_eq_head hne hlist
    rw [h_head]; exact List.All.head h_no_ws hlist
  have hback : (Nat.repr n).back.isWhitespace = false := by
    have h_last := String.back_eq_getLast hne hlist
    rw [h_last]; exact List.All.getLast h_no_ws hlist
  exact trim_eq_self_of_nonWhitespace_ends _ hne hfront hback

theorem String.foldl_ofList {α : Type _} (f : α → Char → α) (init : α) :
    ∀ l : List Char, String.foldl f init (String.ofList l) = List.foldl f init l := by
  intro l
  show String.foldlAux f (String.ofList l) (String.ofList l).rawEndPos 0 init = l.foldl f init
  rw [show (0 : String.Pos.Raw) = (⟨utf8SizeSum ([] : List Char)⟩ : String.Pos.Raw) from rfl,
      show String.ofList l = String.ofList ([] ++ l) from by simp]
  exact foldlAux_suffix f [] l init

theorem String.all_ofList (p : Char → Bool) :
    ∀ l : List Char, (String.ofList l).all p = l.all p := by
  intro l
  -- String.all s p = !String.any s (fun c => !p c)
  -- String.any s q = String.anyAux s s.rawEndPos q 0
  unfold String.all String.any
  -- Goal: !(anyAux (ofList l) (ofList l).rawEndPos (fun c => !p c) 0) = l.all p
  congr 1
  rw [show (0 : String.Pos.Raw) = (⟨utf8SizeSum ([] : List Char)⟩ : String.Pos.Raw) from rfl,
      show String.ofList l = String.ofList ([] ++ l) from by simp]
  rw [anyAux_suffix (fun c => !p c) [] l]
  -- Goal: l.any (fun c => !p c) = !l.all p
  simp [List.any_eq_not_all_not]

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

theorem toNat?_repr (n : Nat) : String.toNat? (Nat.repr n) = some n := by
  have h_isNat := repr_isNat n
  simp only [String.toNat?, h_isNat, ite_true]
  -- Goal: some ((Nat.repr n).foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0) = some n
  congr 1
  rw [repr_eq_ofList, String.foldl_ofList]
  -- Goal: (Nat.toDigits 10 n).foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0 = n
  -- This is decodeDigits since digitValue c = c.toNat - '0'.toNat
  show decodeDigits (Nat.toDigits 10 n) = n
  exact decodeDigits_toDigits n

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
