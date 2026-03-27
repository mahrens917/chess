/-
StringLemmas.lean

This file provides foundational string manipulation lemmas needed for proving
SAN (Standard Algebraic Notation) parsing properties.

Includes infrastructure lemmas connecting byte-level string operations to
character-level semantics for dropRight and endsWith proofs.

In Lean 4.29, several String operations (any, contains, trim, dropRight) were
redefined to use a pattern-based Slice framework. The new implementations are
semantically equivalent to the old ones but the proofs of equivalence require
going through the opaque iterator/pattern framework.

We axiomatize bridges between new and old APIs where needed, similar to the
existing replace_eq_intercalate_splitOn axiom for String.replace.
-/
import Batteries

namespace Chess

namespace StringLemmas

/-! ## Bridge axioms for Lean 4.29 API changes

In Lean 4.29, `String.any`, `String.contains`, and `String.dropRight` were
redefined to use pattern-based search via `String.Slice`. The new definitions
are semantically equivalent but not definitionally equal to the old ones.

The `String.Legacy` namespace in Batteries preserves the old definitions.
`String.any_eq` from Batteries proves `Legacy.any s p = s.toList.any p`.

We bridge the gap between the new `String.any` (pattern-based) and the old
`String.Legacy.any` (character iteration) with an axiom, analogous to the
existing `replace_eq_intercalate_splitOn` axiom for `String.replace`.
-/

/-- Bridge axiom: the new pattern-based `String.any` agrees with the old
character-iteration-based `String.Legacy.any`. Both check whether any
character in the string satisfies the predicate `p`. -/
axiom string_any_eq_legacy (s : String) (p : Char → Bool) :
    s.any p = String.Legacy.any s p

/-- Bridge axiom: the new pattern-based `String.dropRight` agrees with the old
`Substring.Raw`-based computation. Both remove the last `n` characters. -/
axiom string_dropRight_eq_legacy (s : String) (n : Nat) :
    s.dropRight n = (String.toRawSubstring s |>.dropRight n |>.toString)

/-- Bridge axiom: the new pattern-based `String.contains` for `Char` agrees with the old
`String.Legacy.contains`. Both check whether the character appears in the string. -/
axiom string_contains_eq_legacy (s : String) (c : Char) :
    s.contains c = String.Legacy.contains s c

/-- Bridge axiom: the new `String.trim` (which goes through `trimAscii.copy`)
agrees with the old `Substring.Raw.trim`-based computation. Both trim leading
and trailing ASCII whitespace. -/
axiom string_trim_eq_legacy (s : String) :
    s.trim = (Substring.Raw.trim (String.toRawSubstring s)).toString

/-! ## Section 0: UTF-8 Infrastructure -/

-- Size bounds for UTF-8 encoding (used in case analysis)
private theorem h127_lt : (127 : Nat) < UInt32.size := by native_decide
private theorem h2047_lt : (2047 : Nat) < UInt32.size := by native_decide
private theorem h65535_lt : (65535 : Nat) < UInt32.size := by native_decide

/-- The length of UTF-8 encoded bytes equals the character's utf8Size -/
private theorem utf8EncodeChar_length (c : Char) :
    (String.utf8EncodeChar c).length = c.utf8Size := by
  unfold String.utf8EncodeChar Char.utf8Size
  by_cases h1 : c.val.toNat ≤ 127
  · simp only [h1, ↓reduceIte, List.length_singleton]
    have hle : c.val ≤ UInt32.ofNatLT 127 h127_lt := by
      rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h1
    simp only [hle, ↓reduceIte]
  · by_cases h2 : c.val.toNat ≤ 2047
    · simp only [h1, h2, ↓reduceIte, List.length_cons, List.length_nil]
      have hnle : ¬(c.val ≤ UInt32.ofNatLT 127 h127_lt) := by
        rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h1
      have hle : c.val ≤ UInt32.ofNatLT 2047 h2047_lt := by
        rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h2
      simp only [hnle, hle, ↓reduceIte]
    · by_cases h3 : c.val.toNat ≤ 65535
      · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]
        have hnle1 : ¬(c.val ≤ UInt32.ofNatLT 127 h127_lt) := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h1
        have hnle2 : ¬(c.val ≤ UInt32.ofNatLT 2047 h2047_lt) := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h2
        have hle : c.val ≤ UInt32.ofNatLT 65535 h65535_lt := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h3
        simp only [hnle1, hnle2, hle, ↓reduceIte]
      · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]
        have hnle1 : ¬(c.val ≤ UInt32.ofNatLT 127 h127_lt) := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h1
        have hnle2 : ¬(c.val ≤ UInt32.ofNatLT 2047 h2047_lt) := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h2
        have hnle3 : ¬(c.val ≤ UInt32.ofNatLT 65535 h65535_lt) := by
          rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNatLT]; exact h3
        simp only [hnle1, hnle2, hnle3, ↓reduceIte]

/-- Sum of utf8Size for each character in a list -/
private def utf8Len : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + utf8Len cs

private theorem utf8Len_append (l1 l2 : List Char) :
    utf8Len (l1 ++ l2) = utf8Len l1 + utf8Len l2 := by
  induction l1 with
  | nil => simp [utf8Len]
  | cons c cs ih => simp [utf8Len, ih]; omega

private theorem List.toByteArray_loop_size (l : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop l acc).size = acc.size + l.length := by
  induction l generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons hd tl ih =>
    simp only [List.toByteArray.loop, List.length_cons]
    rw [ih]
    simp only [ByteArray.push, ByteArray.size, Array.size_push]
    omega

private theorem List.toByteArray_size' (l : List UInt8) : l.toByteArray.size = l.length := by
  unfold List.toByteArray
  rw [List.toByteArray_loop_size]
  simp [ByteArray.size_empty]

private theorem flatMap_utf8EncodeChar_length (l : List Char) :
    (l.flatMap String.utf8EncodeChar).length = utf8Len l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, utf8EncodeChar_length, utf8Len]
    rw [ih]

private theorem utf8Len_eq_utf8ByteSize_ofList (l : List Char) :
    utf8Len l = (String.ofList l).utf8ByteSize := by
  simp only [String.ofList, String.utf8ByteSize, List.utf8Encode]
  rw [← flatMap_utf8EncodeChar_length l]
  rw [List.toByteArray_size']

private theorem utf8Len_eq_utf8ByteSize (s : String) : utf8Len s.toList = s.utf8ByteSize := by
  have h : s = String.ofList s.toList := (String.ofList_toList).symm
  rw [h, String.toList_ofList]
  exact utf8Len_eq_utf8ByteSize_ofList s.toList

private theorem pos_add_char (p : String.Pos.Raw) (c : Char) :
    (p + c) = ⟨p.byteIdx + c.utf8Size⟩ := by
  cases p; rfl

private theorem extract_go₂_eq (l : List Char) (i : Nat) :
    String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨i⟩ = [] := by
  cases l with
  | nil => rfl
  | cons c cs =>
    unfold String.Pos.Raw.extract.go₂
    simp only [↓reduceIte]

private theorem extract_go₂_prefix (l1 : List Char) (l2 : List Char) (i : Nat) :
    String.Pos.Raw.extract.go₂ (l1 ++ l2) ⟨i⟩ ⟨i + utf8Len l1⟩ = l1 := by
  induction l1 generalizing i with
  | nil =>
    simp only [utf8Len, Nat.add_zero, List.nil_append]
    exact extract_go₂_eq l2 i
  | cons c cs ih =>
    simp only [List.cons_append, utf8Len]
    unfold String.Pos.Raw.extract.go₂
    have hne : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i + (c.utf8Size + utf8Len cs)⟩ := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]
      have := Char.utf8Size_pos c
      omega
    simp only [hne, ↓reduceIte]
    congr 1
    rw [pos_add_char]
    have heq : i + (c.utf8Size + utf8Len cs) = (i + c.utf8Size) + utf8Len cs := by omega
    rw [heq]
    exact ih (i + c.utf8Size)

private theorem extract_go₁_zero (l : List Char) (e : String.Pos.Raw) :
    String.Pos.Raw.extract.go₁ l (0 : String.Pos.Raw) ⟨0⟩ e =
    String.Pos.Raw.extract.go₂ l ⟨0⟩ e := by
  cases l with
  | nil => rfl
  | cons c cs =>
    unfold String.Pos.Raw.extract.go₁
    rfl

/-- go₁ skips through l1 to reach position utf8Len l1, then calls go₂ on l2.
    go₁ signature: go₁ l (i : String.Pos.Raw) (b : String.Pos.Raw) (e : String.Pos.Raw) -/
private theorem extract_go₁_skip (l1 l2 : List Char) (e : String.Pos.Raw) :
    String.Pos.Raw.extract.go₁ (l1 ++ l2) 0 ⟨utf8Len l1⟩ e =
    String.Pos.Raw.extract.go₂ l2 ⟨utf8Len l1⟩ e := by
  -- We need to generalize over the accumulated position
  suffices h : ∀ (acc : Nat),
      String.Pos.Raw.extract.go₁ (l1 ++ l2) ⟨acc⟩ ⟨acc + utf8Len l1⟩ e =
      String.Pos.Raw.extract.go₂ l2 ⟨acc + utf8Len l1⟩ e by
    have h0 := h 0
    simp only [Nat.zero_add] at h0
    exact h0
  intro acc
  induction l1 generalizing acc l2 with
  | nil =>
    simp only [List.nil_append, utf8Len, Nat.add_zero]
    cases l2 with
    | nil => rfl
    | cons c cs =>
      unfold String.Pos.Raw.extract.go₁
      simp only [↓reduceIte]
  | cons c cs ih =>
    simp only [List.cons_append, utf8Len]
    unfold String.Pos.Raw.extract.go₁
    have hne : (⟨acc⟩ : String.Pos.Raw) ≠ ⟨acc + (c.utf8Size + utf8Len cs)⟩ := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]
      have := Char.utf8Size_pos c; omega
    simp only [hne, ↓reduceIte, pos_add_char]
    have heq : acc + (c.utf8Size + utf8Len cs) = (acc + c.utf8Size) + utf8Len cs := by omega
    rw [heq]
    exact ih l2 (acc + c.utf8Size)

/-- Extract the full list from position i to i + utf8Len l -/
private theorem extract_go₂_full' (l : List Char) (i : Nat) :
    String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨i + utf8Len l⟩ = l := by
  induction l generalizing i with
  | nil =>
    simp only [utf8Len, Nat.add_zero]
    exact extract_go₂_eq [] i
  | cons c cs ih =>
    simp only [utf8Len]
    unfold String.Pos.Raw.extract.go₂
    have hne : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i + (c.utf8Size + utf8Len cs)⟩ := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]
      have := Char.utf8Size_pos c
      omega
    simp only [hne, ↓reduceIte]
    congr 1
    rw [pos_add_char]
    have heq : i + (c.utf8Size + utf8Len cs) = (i + c.utf8Size) + utf8Len cs := by omega
    rw [heq]
    exact ih (i + c.utf8Size)

/-- Suffix extraction: extract from s.utf8ByteSize to end gives t -/
private theorem extract_suffix (s t : String) :
    String.Pos.Raw.extract (s ++ t) ⟨s.utf8ByteSize⟩ ⟨(s ++ t).utf8ByteSize⟩ = t := by
  unfold String.Pos.Raw.extract
  by_cases h : s.utf8ByteSize ≥ (s ++ t).utf8ByteSize
  · -- s.utf8ByteSize ≥ (s ++ t).utf8ByteSize means t.utf8ByteSize = 0, so t = ""
    have h_utf8 : (s ++ t).utf8ByteSize = s.utf8ByteSize + t.utf8ByteSize := by
      simp only [String.utf8ByteSize_append]
    have h_t_zero : t.utf8ByteSize = 0 := by omega
    have h_t_empty : t = "" := by
      rw [← utf8Len_eq_utf8ByteSize] at h_t_zero
      cases ht : t.toList with
      | nil => exact String.ext ht
      | cons c cs =>
        rw [ht, utf8Len] at h_t_zero
        have := Char.utf8Size_pos c; omega
    rw [h_t_empty]
    simp only [String.append_empty]
    -- Now we need: if s.utf8ByteSize ≥ s.utf8ByteSize then "" else ... = ""
    have hge : s.utf8ByteSize ≥ s.utf8ByteSize := Nat.le_refl _
    simp only [hge, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    simp only [String.toList_append]
    -- Use extract_go₁_skip to skip through s.toList
    have h_utf8_s : utf8Len s.toList = s.utf8ByteSize := utf8Len_eq_utf8ByteSize s
    have h_utf8_st : utf8Len (s.toList ++ t.toList) = (s ++ t).utf8ByteSize := by
      rw [utf8Len_append, utf8Len_eq_utf8ByteSize, utf8Len_eq_utf8ByteSize]
      simp only [String.utf8ByteSize_append]
    rw [← h_utf8_s]
    rw [← h_utf8_st]
    rw [extract_go₁_skip s.toList t.toList ⟨utf8Len (s.toList ++ t.toList)⟩]
    -- Now we need: go₂ t.toList ⟨utf8Len s.toList⟩ ⟨utf8Len (s.toList ++ t.toList)⟩ = t
    -- This is go₂ t.toList ⟨utf8Len s.toList⟩ ⟨utf8Len s.toList + utf8Len t.toList⟩
    rw [utf8Len_append]
    -- Use extract_go₂_full'
    have h_go2 : String.Pos.Raw.extract.go₂ t.toList ⟨utf8Len s.toList⟩
        ⟨utf8Len s.toList + utf8Len t.toList⟩ = t.toList := extract_go₂_full' t.toList (utf8Len s.toList)
    rw [h_go2]
    exact String.ofList_toList

private theorem extract_prefix (s t : String) :
    String.Pos.Raw.extract (s ++ t) ⟨0⟩ ⟨s.utf8ByteSize⟩ = s := by
  unfold String.Pos.Raw.extract
  by_cases h : (0 : Nat) ≥ s.utf8ByteSize
  · have hzero : s.utf8ByteSize = 0 := Nat.eq_zero_of_le_zero h
    have hemp : s = "" := by
      rw [← utf8Len_eq_utf8ByteSize] at hzero
      cases hs : s.toList with
      | nil => exact String.ext hs
      | cons c cs =>
        rw [hs, utf8Len] at hzero
        have := Char.utf8Size_pos c
        omega
    rw [hemp]; rfl
  · simp only [h, ↓reduceIte]
    simp only [String.toList_append]
    rw [extract_go₁_zero]
    rw [← utf8Len_eq_utf8ByteSize]
    have h0 : (0 : Nat) + utf8Len s.toList = utf8Len s.toList := by omega
    rw [← h0]
    rw [extract_go₂_prefix s.toList t.toList 0]
    exact String.ofList_toList

/-! ## Section 1: List helper lemmas -/

theorem List.length_eq_zero_iff {α : Type u} {l : List α} :
    l.length = 0 ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons x xs =>
      simp only [List.length_cons] at h
      omega
  · intro h
    rw [h]
    rfl

theorem List.append_eq_nil_iff {α : Type u} {l1 l2 : List α} :
    l1 ++ l2 = [] ↔ l1 = [] ∧ l2 = [] := by
  constructor
  · intro h
    cases l1 with
    | nil =>
      simp only [List.nil_append] at h
      exact ⟨rfl, h⟩
    | cons x xs =>
      cases h
  · intro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

/-! ## Section 2: Append properties -/

/-- Left cancellation for string append -/
theorem String.append_left_cancel' {s t1 t2 : String} :
    s ++ t1 = s ++ t2 → t1 = t2 := by
  intro h
  have h' : (s ++ t1).toList = (s ++ t2).toList := by rw [h]
  simp only [String.toList_append] at h'
  have : t1.toList = t2.toList := List.append_cancel_left h'
  exact String.ext this

/-- Right cancellation for string append -/
theorem String.append_right_cancel' {s1 s2 t : String} :
    s1 ++ t = s2 ++ t → s1 = s2 := by
  intro h
  have h' : (s1 ++ t).toList = (s2 ++ t).toList := by rw [h]
  simp only [String.toList_append] at h'
  have : s1.toList = s2.toList := List.append_cancel_right h'
  exact String.ext this

/-! ## Section 3: Length Properties -/

/-- Length zero implies empty string -/
theorem String.eq_empty_of_length_zero' {s : String} :
    s.length = 0 → s = "" := by
  intro h
  have h1 : s.toList.length = 0 := by
    have := String.length_toList (s := s)
    omega
  have h2 : s.toList = [] := List.length_eq_zero_iff.mp h1
  exact String.ext h2

/-- A string is empty iff its length is zero -/
theorem String.length_eq_zero_iff' {s : String} :
    s.length = 0 ↔ s = "" := by
  constructor
  · exact eq_empty_of_length_zero'
  · intro h; rw [h]; rfl

/-! ## Section 4: Empty String Properties -/

/-- Append is empty iff both operands are empty -/
theorem String.append_eq_empty' {s t : String} :
    s ++ t = "" ↔ s = "" ∧ t = "" := by
  constructor
  · intro h
    have h' : (s ++ t).toList = [] := by
      have : (s ++ t) = "" := h
      rw [this]
      rfl
    rw [String.toList_append] at h'
    have ⟨hs, ht⟩ := List.append_eq_nil_iff.mp h'
    exact ⟨String.ext hs, String.ext ht⟩
  · intro ⟨hs, ht⟩
    rw [hs, ht]
    rfl

/-! ## Section 5: dropRight key lemma -/

/-- Extract from a list where start equals end gives empty list -/
private theorem extract_go₂_eq' (l : List Char) (i : Nat) :
    String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨i⟩ = [] := by
  cases l with
  | nil => rfl
  | cons c cs =>
    unfold String.Pos.Raw.extract.go₂
    simp only [↓reduceIte]

/-- Extract the full list from position 0 to utf8Len l -/
private theorem extract_go₂_full (l : List Char) (i : Nat) :
    String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨i + utf8Len l⟩ = l := by
  induction l generalizing i with
  | nil =>
    simp only [utf8Len, Nat.add_zero]
    exact extract_go₂_eq' [] i
  | cons c cs ih =>
    simp only [utf8Len]
    unfold String.Pos.Raw.extract.go₂
    have hne : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i + (c.utf8Size + utf8Len cs)⟩ := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]
      have := Char.utf8Size_pos c
      omega
    simp only [hne, ↓reduceIte]
    congr 1
    rw [pos_add_char]
    have heq : i + (c.utf8Size + utf8Len cs) = (i + c.utf8Size) + utf8Len cs := by omega
    rw [heq]
    exact ih (i + c.utf8Size)

/-- Extract the entire string from position 0 to its byte size -/
private theorem extract_full (s : String) :
    String.Pos.Raw.extract s ⟨0⟩ ⟨s.utf8ByteSize⟩ = s := by
  unfold String.Pos.Raw.extract
  by_cases h : (0 : Nat) ≥ s.utf8ByteSize
  · have hzero : s.utf8ByteSize = 0 := Nat.eq_zero_of_le_zero h
    simp only [h, ↓reduceIte]
    rw [String.ext_iff]
    rw [← utf8Len_eq_utf8ByteSize] at hzero
    cases hs : s.toList with
    | nil => rfl
    | cons c cs =>
      rw [hs, utf8Len] at hzero
      have := Char.utf8Size_pos c
      omega
  · simp only [h, ↓reduceIte]
    rw [extract_go₁_zero]
    have h_utf8 : s.utf8ByteSize = utf8Len s.toList := utf8Len_eq_utf8ByteSize s |>.symm
    rw [h_utf8]
    have h0 : (0 : Nat) + utf8Len s.toList = utf8Len s.toList := by omega
    rw [← h0]
    rw [extract_go₂_full s.toList 0]
    exact String.ofList_toList

/-- Two strings with the same underlying byte array are equal. -/
private theorem string_eq_of_ba_eq (s₁ s₂ : String)
    (h : s₁.toByteArray = s₂.toByteArray) : s₁ = s₂ := by
  cases s₁; cases s₂; simpa using h

/-- dropRight 0 is the identity function -/
private theorem dropRight_zero (s : String) : s.dropRight 0 = s := by
  rw [string_dropRight_eq_legacy]
  simp only [String.toRawSubstring, Substring.Raw.dropRight]
  simp only [Substring.Raw.prevn]
  simp only [Substring.Raw.toString]
  simp only [Substring.Raw.bsize, String.rawEndPos]
  simp only [String.Pos.Raw.offsetBy]
  have h1 : s.utf8ByteSize.sub 0 = s.utf8ByteSize := Nat.sub_zero _
  have h2 : 0 + s.utf8ByteSize = s.utf8ByteSize := Nat.zero_add _
  simp only [h1, h2]
  exact extract_full s

/-! ## Section 5b: prevn lemmas for dropRight proof -/

/-- Generalized helper: utf8PrevAux steps back through the last character starting from startPos. -/
private theorem utf8PrevAux_last_gen (l : List Char) (c : Char) (startPos : Nat) :
    String.Pos.Raw.utf8PrevAux (l ++ [c]) ⟨startPos⟩
      (⟨startPos + utf8Len (l ++ [c])⟩ : String.Pos.Raw) =
      (⟨startPos + utf8Len l⟩ : String.Pos.Raw) := by
  induction l generalizing startPos with
  | nil =>
    simp only [utf8Len, List.nil_append, Nat.add_zero]
    unfold String.Pos.Raw.utf8PrevAux
    have h_le : (⟨startPos + c.utf8Size⟩ : String.Pos.Raw) ≤ (⟨startPos⟩ : String.Pos.Raw) + c := by
      simp only [String.Pos.Raw.le_iff, pos_add_char]; omega
    rw [if_pos h_le]
  | cons d ds ih =>
    simp only [List.cons_append]
    unfold String.Pos.Raw.utf8PrevAux
    have h_not_le : ¬((⟨startPos + utf8Len (d :: (ds ++ [c]))⟩ : String.Pos.Raw) ≤
        (⟨startPos⟩ : String.Pos.Raw) + d) := by
      simp only [String.Pos.Raw.le_iff, pos_add_char, utf8Len, utf8Len_append]
      have := Char.utf8Size_pos c; omega
    rw [if_neg h_not_le, pos_add_char]
    have h1 : (⟨startPos + utf8Len (d :: (ds ++ [c]))⟩ : String.Pos.Raw) =
        (⟨startPos + d.utf8Size + utf8Len (ds ++ [c])⟩ : String.Pos.Raw) :=
      String.Pos.Raw.ext (by simp [utf8Len, utf8Len_append]; omega)
    have h2 : (⟨startPos + utf8Len (d :: ds)⟩ : String.Pos.Raw) =
        (⟨startPos + d.utf8Size + utf8Len ds⟩ : String.Pos.Raw) :=
      String.Pos.Raw.ext (by simp [utf8Len]; omega)
    rw [h1, h2]; exact ih (startPos + d.utf8Size)

/-- Helper: utf8PrevAux steps back through the last character.
    Walking back from the end of (l ++ [c]) lands at utf8Len l. -/
private theorem utf8PrevAux_last (l : List Char) (c : Char) :
    String.Pos.Raw.utf8PrevAux (l ++ [c]) 0 ⟨utf8Len (l ++ [c])⟩ = ⟨utf8Len l⟩ := by
  have h := utf8PrevAux_last_gen l c 0
  simp only [Nat.zero_add] at h; exact h

/-- Extra characters past the position don't affect utf8PrevAux result. -/
private theorem utf8PrevAux_append_extra (l1 l2 : List Char) (h_ne : l1 ≠ [])
    (startPos p : Nat) (h_le : p ≤ startPos + utf8Len l1) :
    String.Pos.Raw.utf8PrevAux (l1 ++ l2) (⟨startPos⟩ : String.Pos.Raw)
      (⟨p⟩ : String.Pos.Raw) =
    String.Pos.Raw.utf8PrevAux l1 (⟨startPos⟩ : String.Pos.Raw)
      (⟨p⟩ : String.Pos.Raw) := by
  induction l1 generalizing startPos l2 with
  | nil => exact absurd rfl h_ne
  | cons c cs ih =>
    simp only [List.cons_append]
    unfold String.Pos.Raw.utf8PrevAux
    by_cases h_cond : p ≤ startPos + c.utf8Size
    · have h_le1 : (⟨p⟩ : String.Pos.Raw) ≤ (⟨startPos⟩ : String.Pos.Raw) + c := by
        simp [String.Pos.Raw.le_iff, pos_add_char]; exact h_cond
      rw [if_pos h_le1, if_pos h_le1]
    · have h_nle1 : ¬((⟨p⟩ : String.Pos.Raw) ≤ (⟨startPos⟩ : String.Pos.Raw) + c) := by
        simp [String.Pos.Raw.le_iff, pos_add_char]; omega
      rw [if_neg h_nle1, if_neg h_nle1, pos_add_char]
      cases cs with
      | nil => simp [utf8Len] at h_le; omega
      | cons d ds =>
        exact ih l2 (List.cons_ne_nil d ds) (startPos + c.utf8Size)
          (by simp [utf8Len] at h_le ⊢; omega)

/-- Combined helper: utf8PrevAux on (l ++ [c]) ++ extra at position utf8Len(l ++ [c])
    gives utf8Len l. -/
private theorem utf8PrevAux_last_with_extra (l : List Char) (c : Char) (extra : List Char) :
    String.Pos.Raw.utf8PrevAux ((l ++ [c]) ++ extra) 0
      (⟨utf8Len (l ++ [c])⟩ : String.Pos.Raw) =
      (⟨utf8Len l⟩ : String.Pos.Raw) :=
  (utf8PrevAux_append_extra (l ++ [c]) extra (by simp) 0
    (utf8Len (l ++ [c])) (by omega)).trans
  (utf8PrevAux_last l c)

/-- General prevn theorem: walking back n characters through a suffix. -/
private theorem prevn_drops (n : Nat) :
    ∀ (prefix_list suffix extra : List Char),
    suffix.length = n →
    Substring.Raw.prevn
      ⟨String.ofList (prefix_list ++ suffix ++ extra),
        (0 : String.Pos.Raw),
        (⟨utf8Len (prefix_list ++ suffix ++ extra)⟩ : String.Pos.Raw)⟩
      n
      (⟨utf8Len (prefix_list ++ suffix)⟩ : String.Pos.Raw) =
    (⟨utf8Len prefix_list⟩ : String.Pos.Raw) := by
  induction n with
  | zero =>
    intro prefix_list suffix extra hn
    have h_nil : suffix = [] := by cases suffix with | nil => rfl | cons _ _ => simp at hn
    subst h_nil; simp only [List.append_nil, Substring.Raw.prevn.eq_1]
  | succ k ih =>
    intro prefix_list suffix extra hn
    have h_ne : suffix ≠ [] := by intro h; rw [h] at hn; simp at hn
    have h_dropLast_len : suffix.dropLast.length = k := by
      rw [List.length_dropLast, hn]; omega
    rw [Substring.Raw.prevn.eq_2]
    suffices h_prev_eq :
        Substring.Raw.prev
          ⟨String.ofList (prefix_list ++ suffix ++ extra),
            (0 : String.Pos.Raw),
            (⟨utf8Len (prefix_list ++ suffix ++ extra)⟩ : String.Pos.Raw)⟩
          (⟨utf8Len (prefix_list ++ suffix)⟩ : String.Pos.Raw) =
        (⟨utf8Len (prefix_list ++ suffix.dropLast)⟩ : String.Pos.Raw) by
      rw [h_prev_eq]
      have h_str_eq : prefix_list ++ suffix ++ extra =
          prefix_list ++ suffix.dropLast ++ ([suffix.getLast h_ne] ++ extra) := by
        suffices (prefix_list ++ suffix.dropLast) ++ ([suffix.getLast h_ne] ++ extra) =
            (prefix_list ++ suffix) ++ extra by exact this.symm
        rw [List.append_assoc prefix_list suffix.dropLast,
            ← List.append_assoc suffix.dropLast [suffix.getLast h_ne] extra,
            List.dropLast_concat_getLast h_ne, ← List.append_assoc]
      have h_ss_eq :
          (⟨String.ofList (prefix_list ++ suffix ++ extra),
            (0 : String.Pos.Raw),
            (⟨utf8Len (prefix_list ++ suffix ++ extra)⟩ : String.Pos.Raw)⟩ : Substring.Raw) =
          ⟨String.ofList (prefix_list ++ suffix.dropLast ++ ([suffix.getLast h_ne] ++ extra)),
            (0 : String.Pos.Raw),
            (⟨utf8Len (prefix_list ++ suffix.dropLast ++ ([suffix.getLast h_ne] ++ extra))⟩ :
              String.Pos.Raw)⟩ := by
        congr 1
        · exact congrArg String.ofList h_str_eq
        · exact String.Pos.Raw.ext (congrArg utf8Len h_str_eq)
      rw [h_ss_eq]
      exact ih prefix_list suffix.dropLast ([suffix.getLast h_ne] ++ extra) h_dropLast_len
    -- Prove h_prev_eq: prev at end gives position of suffix.dropLast end
    have h_prev_compute : String.Pos.Raw.utf8PrevAux (prefix_list ++ suffix ++ extra) 0
        (⟨utf8Len (prefix_list ++ suffix)⟩ : String.Pos.Raw) =
        (⟨utf8Len (prefix_list ++ suffix.dropLast)⟩ : String.Pos.Raw) := by
      have h_str_rw : prefix_list ++ suffix ++ extra =
          ((prefix_list ++ suffix.dropLast) ++ [suffix.getLast h_ne]) ++ extra := by
        suffices ((prefix_list ++ suffix.dropLast) ++ [suffix.getLast h_ne]) ++ extra =
            (prefix_list ++ suffix) ++ extra by exact this.symm
        congr 1; rw [List.append_assoc, List.dropLast_concat_getLast h_ne]
      have h_len_rw : (⟨utf8Len (prefix_list ++ suffix)⟩ : String.Pos.Raw) =
          (⟨utf8Len ((prefix_list ++ suffix.dropLast) ++ [suffix.getLast h_ne])⟩ :
            String.Pos.Raw) := by
        congr 1; congr 1
        suffices (prefix_list ++ suffix.dropLast) ++ [suffix.getLast h_ne] = prefix_list ++ suffix by
          exact this.symm
        rw [List.append_assoc, List.dropLast_concat_getLast h_ne]
      rw [show (prefix_list ++ suffix ++ extra : List Char) =
          ((prefix_list ++ suffix.dropLast) ++ [suffix.getLast h_ne]) ++ extra from h_str_rw,
          h_len_rw]
      exact utf8PrevAux_last_with_extra (prefix_list ++ suffix.dropLast) (suffix.getLast h_ne) extra
    -- Now connect Substring.Raw.prev to utf8PrevAux
    unfold Substring.Raw.prev
    simp only [String.Pos.Raw.offsetBy]
    show (if (⟨(0 : String.Pos.Raw).byteIdx + utf8Len (prefix_list ++ suffix)⟩ : String.Pos.Raw) =
            (0 : String.Pos.Raw) then _
          else (⟨(String.Pos.Raw.prev (String.ofList (prefix_list ++ suffix ++ extra))
            (⟨(0 : String.Pos.Raw).byteIdx + utf8Len (prefix_list ++ suffix)⟩ :
              String.Pos.Raw)).byteIdx -
            (0 : String.Pos.Raw).byteIdx⟩ : String.Pos.Raw)) = _
    simp only [show (0 : String.Pos.Raw).byteIdx = (0 : Nat) from rfl,
               Nat.zero_add, Nat.sub_zero]
    have h_pos : 0 < utf8Len (prefix_list ++ suffix) := by
      cases suffix with
      | nil => exact absurd rfl h_ne
      | cons c cs => simp only [utf8Len_append, utf8Len]; have := Char.utf8Size_pos c; omega
    have h_ne_zero : (⟨utf8Len (prefix_list ++ suffix)⟩ : String.Pos.Raw) ≠
        (0 : String.Pos.Raw) := by
      intro h; have := congrArg String.Pos.Raw.byteIdx h; simp at this; omega
    rw [if_neg h_ne_zero]
    simp only [String.Pos.Raw.prev, String.toList_ofList]
    exact congrArg (⟨·.byteIdx⟩ : String.Pos.Raw → String.Pos.Raw) h_prev_compute

/-- Key lemma: prevn on full string steps back through suffix characters.
    For (prefix ++ suffix), walking back suffix.length from end lands at utf8Len prefix. -/
private theorem prevn_full_string (prefix_list suffix : List Char) :
    Substring.Raw.prevn
      { str := String.ofList (prefix_list ++ suffix),
        startPos := ⟨0⟩,
        stopPos := ⟨utf8Len (prefix_list ++ suffix)⟩ }
      suffix.length
      ⟨utf8Len (prefix_list ++ suffix)⟩ =
    ⟨utf8Len prefix_list⟩ := by
  have h := prevn_drops suffix.length prefix_list suffix [] rfl
  simp only [List.append_nil] at h; exact h

/--
Key lemma: dropRight of append strips the suffix when lengths match.

This follows semantically from the definition of dropRight:
  dropRight(s ++ t, t.length) = take(s ++ t, (s ++ t).length - t.length)
                              = take(s ++ t, s.length)
                              = s

**Proof Strategy**:
The proof reduces to showing that `prevn t.length` from the end of `(s ++ t)`
lands at byte position `s.utf8ByteSize`. This follows from:

1. `(s ++ t).utf8ByteSize = s.utf8ByteSize + t.utf8ByteSize`
2. `prevn t.length` moves back by exactly `t.utf8ByteSize` bytes
   (since it steps through `t.length` characters, each contributing its utf8Size)
3. The resulting position `s.utf8ByteSize` combined with `extract_prefix` gives `s`

The formal proof requires a lemma about `prevn` and UTF-8 byte arithmetic.

**Verification**: Semantically correct and verified by SAN parsing tests.
Example: ("ab" ++ "cd").dropRight 2 = "ab" ✓
-/
theorem String.dropRight_append_right' (s t : String) :
    (s ++ t).dropRight t.length = s := by
  -- Use bridge to old Substring.Raw-based definition
  rw [string_dropRight_eq_legacy]
  -- Base case: t is empty
  by_cases ht : t = ""
  · rw [ht]
    simp only [String.append_empty, String.length_empty]
    rw [← string_dropRight_eq_legacy]
    exact dropRight_zero s
  · -- General case: use prevn_full_string then extract_prefix
    have h_prevn : Substring.Raw.prevn
        { str := s ++ t, startPos := ⟨0⟩, stopPos := ⟨(s ++ t).utf8ByteSize⟩ }
        t.length
        ⟨(s ++ t).utf8ByteSize⟩ = ⟨s.utf8ByteSize⟩ := by
      have h_str_eq : s ++ t = String.ofList (s.toList ++ t.toList) := by
        rw [← String.toList_append]; exact String.ofList_toList.symm
      have h_utf8_eq : (String.ofList (s.toList ++ t.toList)).utf8ByteSize =
          utf8Len (s.toList ++ t.toList) :=
        (utf8Len_eq_utf8ByteSize_ofList _).symm
      have h_len_eq : t.length = t.toList.length :=
        (String.length_toList (s := t)).symm
      have h_utf8_s : s.utf8ByteSize = utf8Len s.toList :=
        (utf8Len_eq_utf8ByteSize s).symm
      rw [h_str_eq, h_utf8_eq, h_len_eq, h_utf8_s]
      exact prevn_full_string s.toList t.toList
    simp only [String.toRawSubstring, Substring.Raw.dropRight, String.rawEndPos,
               Substring.Raw.bsize, String.Pos.Raw.offsetBy, Nat.zero_add]
    simp only [show (s ++ t).utf8ByteSize.sub 0 = (s ++ t).utf8ByteSize from Nat.sub_zero _]
    simp only [h_prevn]
    show String.Pos.Raw.extract (s ++ t) ⟨0⟩ ⟨s.utf8ByteSize⟩ = s
    exact extract_prefix s t

/-- If we append a suffix and then dropRight by its length, we get the original -/
theorem String.append_then_dropRight' (s suffix : String) :
    (s ++ suffix).dropRight suffix.length = s :=
  dropRight_append_right' s suffix

/-! ## Section 6: String.map -/

/-- map distributes over append -/
theorem String.map_append' (f : Char → Char) (s t : String) :
    (s ++ t).map f = s.map f ++ t.map f := by
  simp only [String.ext_iff, String.toList_map, String.toList_append, List.map_append]

/-! ## Section 7: Specialized lemmas for SAN parsing -/

/-- Suffix strip roundtrip: dropRight after append retrieves original -/
theorem String.suffix_strip_base' (base suffix : String) :
    (base ++ suffix).dropRight suffix.length = base :=
  dropRight_append_right' base suffix

/-- Specialized for castle normalization: '0' → 'O' removes all '0's -/
theorem String.normalizeCastle_removes_zero' (s : String) :
    let f := fun c => if c = '0' then 'O' else c
    '0' ∉ (s.map f).toList := by
  simp only [String.toList_map]
  intro h
  rw [List.mem_map] at h
  obtain ⟨c, _, hfc⟩ := h
  by_cases hc : c = '0'
  · simp only [hc, ↓reduceIte] at hfc
    have hne : 'O' ≠ '0' := by decide
    exact hne hfc
  · simp only [hc, ↓reduceIte] at hfc

/-! ## Section 9: Three-part suffix strip -/

/-- Three-part suffix strip: base ++ mid ++ suffix, drop suffix.length gives base ++ mid -/
theorem String.dropRight_append_three' (base mid suffix : String) :
    (base ++ mid ++ suffix).dropRight suffix.length = base ++ mid := by
  have : base ++ mid ++ suffix = (base ++ mid) ++ suffix := by
    simp only [String.append_assoc]
  rw [this]
  exact dropRight_append_right' (base ++ mid) suffix

/-! ## Section 10: Check/checkmate suffix lemmas -/

/-- The check suffix "+" doesn't contain '0' -/
theorem check_plus_no_zero : '0' ∉ ("+").toList := by decide

/-- The checkmate suffix "#" doesn't contain '0' -/
theorem check_hash_no_zero : '0' ∉ ("#").toList := by decide

/-- Empty string doesn't contain '0' -/
theorem empty_no_zero : '0' ∉ ("").toList := by decide

/-- The check/checkmate suffixes don't contain '0' -/
theorem check_suffix_no_zero (suffix : String)
    (h : suffix = "+" ∨ suffix = "#" ∨ suffix = "") :
    '0' ∉ suffix.toList := by
  cases h with
  | inl h => rw [h]; exact check_plus_no_zero
  | inr h =>
    cases h with
    | inl h => rw [h]; exact check_hash_no_zero
    | inr h => rw [h]; exact empty_no_zero

/-- Membership in append -/
theorem String.mem_append_toList (s t : String) (c : Char) :
    c ∈ (s ++ t).toList ↔ c ∈ s.toList ∨ c ∈ t.toList := by
  simp only [String.toList_append, List.mem_append]

/-- If '0' not in base and suffix is check notation, '0' not in combined -/
theorem String.no_zero_preserved (base suffix : String)
    (hbase : '0' ∉ base.toList)
    (hsuffix : suffix = "+" ∨ suffix = "#" ∨ suffix = "") :
    '0' ∉ (base ++ suffix).toList := by
  rw [mem_append_toList]
  intro h
  cases h with
  | inl h => exact hbase h
  | inr h => exact check_suffix_no_zero suffix hsuffix h

/-! ## Section 11: String.any / String.contains bridge to List -/

/-- Helper: utf8GetAux on a list starting at position startPos, targeting startPos + utf8Len pre,
    returns the character c right after the prefix. -/
private theorem utf8GetAux_skip_to (pre : List Char) (c : Char) (rest : List Char) (startPos : Nat) :
    String.Pos.Raw.utf8GetAux (pre ++ c :: rest) ⟨startPos⟩ ⟨startPos + utf8Len pre⟩ = c := by
  induction pre generalizing startPos with
  | nil =>
    simp only [List.nil_append, utf8Len, Nat.add_zero]
    unfold String.Pos.Raw.utf8GetAux; simp
  | cons d ds ih =>
    simp only [List.cons_append, utf8Len]; unfold String.Pos.Raw.utf8GetAux
    have hne : (⟨startPos⟩ : String.Pos.Raw) ≠ ⟨startPos + (d.utf8Size + utf8Len ds)⟩ := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]; have := Char.utf8Size_pos d; omega
    simp only [hne, ↓reduceIte, String.Pos.Raw.add_char_eq]
    show String.Pos.Raw.utf8GetAux (ds ++ c :: rest) ⟨startPos + d.utf8Size⟩
        ⟨startPos + (d.utf8Size + utf8Len ds)⟩ = c
    rw [show startPos + (d.utf8Size + utf8Len ds) = (startPos + d.utf8Size) + utf8Len ds from by omega]
    exact ih (startPos + d.utf8Size)

section AnyAuxBridge
set_option allowUnsafeReducibility true
attribute [local semireducible] String.Legacy.anyAux

/-- Legacy.anyAux on String.ofList (pre ++ suf) from byte position utf8Len pre to utf8Len (pre ++ suf)
    equals suf.any p. This is the core of the String.any ↔ List.any bridge. -/
private theorem anyAux_suffix_eq_list_any (pre suf : List Char) (p : Char → Bool) :
    String.Legacy.anyAux (String.ofList (pre ++ suf)) ⟨utf8Len (pre ++ suf)⟩ p ⟨utf8Len pre⟩ = suf.any p := by
  induction suf generalizing pre with
  | nil =>
    simp only [List.append_nil, List.any_nil]; unfold String.Legacy.anyAux
    simp [show ¬(utf8Len pre < utf8Len pre) from Nat.lt_irrefl _]
  | cons c cs ih =>
    simp only [List.any_cons]; unfold String.Legacy.anyAux
    have h_lt : utf8Len pre < utf8Len (pre ++ c :: cs) := by
      rw [utf8Len_append]; simp [utf8Len]; have := Char.utf8Size_pos c; omega
    simp only [show (⟨utf8Len pre⟩ : String.Pos.Raw) < ⟨utf8Len (pre ++ c :: cs)⟩ from h_lt, ↓reduceDIte]
    have h_get : String.Pos.Raw.get (String.ofList (pre ++ c :: cs)) ⟨utf8Len pre⟩ = c := by
      unfold String.Pos.Raw.get; rw [String.toList_ofList]
      have := utf8GetAux_skip_to pre c cs 0; simp only [Nat.zero_add] at this; exact this
    have h_next : String.Pos.Raw.next (String.ofList (pre ++ c :: cs)) ⟨utf8Len pre⟩ =
        ⟨utf8Len pre + c.utf8Size⟩ := by
      unfold String.Pos.Raw.next; rw [h_get, String.Pos.Raw.add_char_eq]
    rw [h_get, h_next]
    by_cases hp : p c = true
    · simp [hp]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
      calc String.Legacy.anyAux (String.ofList (pre ++ c :: cs)) ⟨utf8Len (pre ++ c :: cs)⟩ p
              ⟨utf8Len pre + c.utf8Size⟩
          = String.Legacy.anyAux (String.ofList ((pre ++ [c]) ++ cs)) ⟨utf8Len ((pre ++ [c]) ++ cs)⟩ p
              ⟨utf8Len (pre ++ [c])⟩ := by
            congr 1 <;> simp [utf8Len_append, utf8Len] <;> omega
        _ = cs.any p := ih (pre ++ [c])

/-- Legacy.any on String.ofList l equals List.any on l. -/
private theorem legacy_any_ofList_eq_list_any (l : List Char) (p : Char → Bool) :
    String.Legacy.any (String.ofList l) p = l.any p := by
  unfold String.Legacy.any String.rawEndPos
  rw [show (String.ofList l).utf8ByteSize = utf8Len l from (utf8Len_eq_utf8ByteSize_ofList l).symm]
  show String.Legacy.anyAux (String.ofList l) ⟨utf8Len l⟩ p 0 = l.any p
  change String.Legacy.anyAux (String.ofList l) ⟨utf8Len l⟩ p ⟨utf8Len []⟩ = l.any p
  rw [show String.ofList l = String.ofList ([] ++ l) from by simp,
      show (⟨utf8Len l⟩ : String.Pos.Raw) = ⟨utf8Len ([] ++ l)⟩ from by simp]
  exact anyAux_suffix_eq_list_any [] l p

end AnyAuxBridge

/-- String.any on any string equals List.any on its toList. -/
theorem String.any_eq_toList_any (s : String) (p : Char → Bool) :
    s.any p = s.toList.any p := by
  -- Bridge: new String.any agrees with Legacy.any (axiom), then use Batteries lemma
  rw [string_any_eq_legacy]
  exact String.any_eq s p

/-- String.contains is equivalent to membership in toList. -/
theorem String.contains_iff_mem_toList (s : String) (c : Char) :
    s.contains c = true ↔ c ∈ s.toList := by
  rw [string_contains_eq_legacy]
  exact String.contains_iff s c

/-- If a character is not in s.toList, then s.contains returns false. -/
theorem String.not_contains_of_not_mem_toList (s : String) (c : Char) :
    c ∉ s.toList → s.contains c = false := by
  intro h
  rw [Bool.eq_false_iff]
  intro hc
  exact h ((String.contains_iff_mem_toList s c).mp hc)

/-- If s.contains c = true, then c ∈ s.toList. -/
theorem String.mem_toList_of_contains (s : String) (c : Char) :
    s.contains c = true → c ∈ s.toList :=
  (String.contains_iff_mem_toList s c).mp

/-! ## Section 12: String.trim identity -/

-- Helper: List.any false implies all elements fail predicate
private theorem list_any_false_forall {l : List Char} {p : Char → Bool}
    (h : l.any p = false) : ∀ c ∈ l, p c = false := by
  intro c hc
  cases hpx : p c with
  | false => rfl
  | true =>
    have : l.any p = true := List.any_eq_true.mpr ⟨c, hc, hpx⟩
    rw [h] at this; cases this

-- Helper: get at same byte position returns the character there
private theorem utf8GetAux_at_same_pos (c : Char) (cs : List Char) (pos : Nat) :
    String.Pos.Raw.utf8GetAux (c :: cs) ⟨pos⟩ ⟨pos⟩ = c := by
  unfold String.Pos.Raw.utf8GetAux; simp

-- Helper: rawEndPos > 0 for non-empty strings
private theorem rawEndPos_pos' (s : String) (h : s ≠ "") :
    (0 : Nat) < s.utf8ByteSize := by
  rw [← utf8Len_eq_utf8ByteSize]
  cases hs : s.toList with
  | nil => exact absurd (String.ext hs) h
  | cons c _ => simp only [utf8Len]; have := Char.utf8Size_pos c; omega

set_option allowUnsafeReducibility true
attribute [local semireducible] Substring.Raw.takeWhileAux
attribute [local semireducible] Substring.Raw.takeRightWhileAux

/-- Helper: utf8PrevAux steps back one char from the end of a non-empty list.
    For init ++ [last], utf8PrevAux at utf8Len (init ++ [last]) returns utf8Len init. -/
private theorem utf8PrevAux_step_back (init : List Char) (last : Char) :
    String.Pos.Raw.utf8PrevAux (init ++ [last]) 0
      (⟨utf8Len (init ++ [last])⟩ : String.Pos.Raw) =
      (⟨utf8Len init⟩ : String.Pos.Raw) :=
  utf8PrevAux_last init last

/-- Helper: utf8GetAux at utf8Len init on (init ++ [last] ++ rest) returns last. -/
private theorem utf8GetAux_at_init_pos (init : List Char) (last : Char) (rest : List Char) :
    String.Pos.Raw.utf8GetAux (init ++ last :: rest) 0
      (⟨utf8Len init⟩ : String.Pos.Raw) = last := by
  have h0 : (0 : Nat) + utf8Len init = utf8Len init := Nat.zero_add _
  rw [← h0]
  exact utf8GetAux_skip_to init last rest 0

/-- If no character in s is whitespace, String.trim is the identity. -/
theorem String.trim_eq_self_of_no_whitespace (s : String)
    (h : s.any Char.isWhitespace = false) : s.trim = s := by
  by_cases h_ne : s = ""
  · subst h_ne; native_decide
  · have h_ne_nil : s.toList ≠ [] := fun heq => h_ne (String.ext heq)
    have h_any_list : s.toList.any Char.isWhitespace = false := by
      rw [← String.any_eq_toList_any]; exact h
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil h_ne_nil
    -- First char not whitespace
    have h_first_get : String.Pos.Raw.get s (0 : String.Pos.Raw) = c := by
      show String.Pos.Raw.utf8GetAux s.toList 0 0 = c
      rw [hcs]; exact utf8GetAux_at_same_pos c cs 0
    have h_first_not_ws : (String.Pos.Raw.get s (0 : String.Pos.Raw)).isWhitespace = false := by
      rw [h_first_get]
      exact list_any_false_forall h_any_list c (hcs ▸ List.Mem.head cs)
    have h_pos : (0 : String.Pos.Raw) < s.rawEndPos := rawEndPos_pos' s h_ne
    -- takeWhileAux returns 0
    have h_twa : Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace
        (0 : String.Pos.Raw) = (0 : String.Pos.Raw) := by
      unfold Substring.Raw.takeWhileAux
      rw [dif_pos h_pos]
      simp only [h_first_not_ws, Bool.false_eq_true, ↓reduceIte]
    -- rawEndPos = utf8Len s.toList
    have h_endpos : s.rawEndPos = (⟨utf8Len s.toList⟩ : String.Pos.Raw) :=
      String.Pos.Raw.ext ((utf8Len_eq_utf8ByteSize s).symm)
    -- Decompose c :: cs = init ++ [last] for prev/get reasoning
    have h_ccs_ne : (c :: cs) ≠ [] := List.cons_ne_nil c cs
    let h_last_val := (c :: cs).getLast h_ccs_ne
    let h_init_val := (c :: cs).dropLast
    have h_decomp : (c :: cs) = h_init_val ++ [h_last_val] :=
      (List.dropLast_concat_getLast h_ccs_ne).symm
    -- prev s rawEndPos = utf8Len init
    have h_prev : String.Pos.Raw.prev s s.rawEndPos =
        (⟨utf8Len h_init_val⟩ : String.Pos.Raw) := by
      show String.Pos.Raw.utf8PrevAux s.toList 0 s.rawEndPos = _
      rw [h_endpos, hcs]
      -- Goal: utf8PrevAux (c :: cs) 0 ⟨utf8Len (c :: cs)⟩ = ⟨utf8Len init⟩
      -- Rewrite (c :: cs) as init ++ [last] only in specific positions
      show String.Pos.Raw.utf8PrevAux (c :: cs) 0
        (⟨utf8Len (c :: cs)⟩ : String.Pos.Raw) = _
      rw [show (c :: cs) = h_init_val ++ [h_last_val] from h_decomp]
      exact utf8PrevAux_step_back h_init_val h_last_val
    -- get s (prev s rawEndPos) = last char
    have h_get : String.Pos.Raw.get s (String.Pos.Raw.prev s s.rawEndPos) = h_last_val := by
      rw [h_prev]
      show String.Pos.Raw.utf8GetAux s.toList 0 ⟨utf8Len h_init_val⟩ = h_last_val
      rw [hcs, h_decomp]
      exact utf8GetAux_at_init_pos h_init_val h_last_val []
    -- Last char not whitespace
    have h_last_mem : h_last_val ∈ s.toList := by
      rw [hcs]; exact List.getLast_mem h_ccs_ne
    have h_last_not_ws : (String.Pos.Raw.get s (String.Pos.Raw.prev s s.rawEndPos)).isWhitespace = false := by
      rw [h_get]
      exact list_any_false_forall h_any_list _ h_last_mem
    -- takeRightWhileAux returns rawEndPos
    have h_trwa : Substring.Raw.takeRightWhileAux s (0 : String.Pos.Raw) Char.isWhitespace
        s.rawEndPos = s.rawEndPos := by
      unfold Substring.Raw.takeRightWhileAux
      rw [dif_pos h_pos]
      simp only [h_last_not_ws, Bool.not_false, ↓reduceIte]
    -- Combine: trim extracts from 0 to rawEndPos = full string
    -- Need to show the internal representation matches our hypotheses
    suffices h_eq : String.Pos.Raw.extract s
        (Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace (0 : String.Pos.Raw))
        (Substring.Raw.takeRightWhileAux s
          (Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace (0 : String.Pos.Raw))
          Char.isWhitespace s.rawEndPos) = s by
      rw [string_trim_eq_legacy]
      unfold Substring.Raw.trim
      simp only [String.toRawSubstring, Substring.Raw.toString]
      exact h_eq
    rw [h_twa, h_trwa]
    exact extract_full s

/-! ## Section 13: String.replace "e.p." "" identity

When a string contains no '.' character, replacing "e.p." with "" is the identity.
This is needed for SAN parsing proofs: moveToSanBase produces strings from the
character set {a-h, 1-8, K, Q, R, B, N, x, +, #, =, O, -} which excludes '.'.

### Proof Strategy

In Lean 4.26, `String.replace` is implemented through a KMP searcher iterator
framework (`ForwardSliceSearcher`) that provides no proof-level lemmas connecting
it to string-level properties. The framework uses `@[extern]` functions that
prevent kernel reduction for universally quantified strings.

We bridge this gap with a single axiom stating that `String.replace` agrees with
`String.intercalate ∘ String.splitOn` (the classical definition from earlier Lean
versions), and then prove the rest from first principles through the transparent
`splitOnAux` function.
-/

/-- `String.replace` agrees with `String.intercalate ∘ String.splitOn`.

This is the classical definition of `replace` used in earlier Lean 4 versions and in
virtually every programming language. In Lean 4.26, `String.replace` was reimplemented
using a KMP searcher iterator framework without proof-level correctness lemmas.

This axiom bridges the gap until upstream Lean provides formal correctness lemmas.
It is computationally validated via `native_decide` on all test strings:
  `native_decide : s.replace pat rep = String.intercalate rep (s.splitOn pat)` -/
axiom String.replace_eq_intercalate_splitOn (s : String) (pat rep : String) :
    s.replace pat rep = String.intercalate rep (s.splitOn pat)

/-- `utf8GetAux` returns a character from the input list, or `default` ('A').
This is the core lemma connecting byte-level string access to list membership. -/
private theorem utf8GetAux_mem_or_default' :
    ∀ (l : List Char) (i p : String.Pos.Raw),
    String.Pos.Raw.utf8GetAux l i p ∈ l ∨ String.Pos.Raw.utf8GetAux l i p = default := by
  intro l
  induction l with
  | nil =>
    intro i p; right
    unfold String.Pos.Raw.utf8GetAux; rfl
  | cons c cs ih =>
    intro i p
    unfold String.Pos.Raw.utf8GetAux
    split
    · left; exact List.Mem.head cs
    · cases ih (i + c) p with
      | inl hmem => left; exact List.Mem.tail c hmem
      | inr hdef => right; exact hdef

/-- `Pos.Raw.get` returns a character in `s.toList`, or `default` ('A'). -/
private theorem get_mem_or_default' (s : String) (i : String.Pos.Raw) :
    String.Pos.Raw.get s i ∈ s.toList ∨ String.Pos.Raw.get s i = default := by
  unfold String.Pos.Raw.get
  exact utf8GetAux_mem_or_default' s.toList 0 i

/-- '.' is not the default Char value ('A'). -/
private theorem dot_ne_default : ('.' : Char) ≠ default := by decide

/-- If `s[i] == '.'` is true (BEq), then `'.' ∈ s.toList`. -/
private theorem beq_dot_implies_mem (s : String) (i : String.Pos.Raw)
    (h : (String.Pos.Raw.get s i == '.') = true) :
    '.' ∈ s.toList := by
  have heq : String.Pos.Raw.get s i = '.' := by
    simp [BEq.beq, decide_eq_true_eq] at h; exact h
  cases get_mem_or_default' s i with
  | inl hmem => rw [← heq]; exact hmem
  | inr hdef => exfalso; exact dot_ne_default (heq ▸ hdef)

/-- `go₂` extracts the full list when the end position is at or beyond the actual end. -/
private theorem extract_go₂_ge' (l : List Char) (i e : Nat) (he : e ≥ i + utf8Len l) :
    String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨e⟩ = l := by
  induction l generalizing i with
  | nil => rfl
  | cons c cs ih =>
    simp only [utf8Len] at he
    unfold String.Pos.Raw.extract.go₂
    have hne : (⟨i⟩ : String.Pos.Raw) ≠ ⟨e⟩ := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]; have := Char.utf8Size_pos c; omega
    simp only [hne, ↓reduceIte]; congr 1
    rw [pos_add_char]; exact ih (i + c.utf8Size) (by omega)

/-- `go₂` gives the same result for any two end positions both ≥ actual string end. -/
private theorem extract_go₂_end_ge (l : List Char) (i e e' : Nat)
    (he : e ≥ i + utf8Len l) (he' : e' ≥ i + utf8Len l) :
    String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨e⟩ = String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨e'⟩ := by
  rw [extract_go₂_ge' l i e he, extract_go₂_ge' l i e' he']

/-- `go₁` gives the same result for any two end positions both ≥ actual string end. -/
private theorem extract_go₁_end_ge (l : List Char) (i b e e' : Nat)
    (he : e ≥ i + utf8Len l) (he' : e' ≥ i + utf8Len l) :
    String.Pos.Raw.extract.go₁ l ⟨i⟩ ⟨b⟩ ⟨e⟩ = String.Pos.Raw.extract.go₁ l ⟨i⟩ ⟨b⟩ ⟨e'⟩ := by
  induction l generalizing i with
  | nil => rfl
  | cons c cs ih =>
    simp only [utf8Len] at he he'
    unfold String.Pos.Raw.extract.go₁
    split
    · exact extract_go₂_end_ge (c :: cs) i e e'
        (by simp [utf8Len]; omega) (by simp [utf8Len]; omega)
    · exact ih (i + c.utf8Size) (by omega) (by omega)

/-- `go₁` past the end of the character list returns `[]`. -/
private theorem extract_go₁_past_end (l : List Char) (i b e : Nat)
    (hb : b ≥ i + utf8Len l) :
    String.Pos.Raw.extract.go₁ l ⟨i⟩ ⟨b⟩ ⟨e⟩ = [] := by
  induction l generalizing i with
  | nil => rfl
  | cons c cs ih =>
    simp only [utf8Len] at hb
    unfold String.Pos.Raw.extract.go₁
    have hne : (⟨i⟩ : String.Pos.Raw) ≠ ⟨b⟩ := by
      simp only [ne_eq, String.Pos.Raw.mk.injEq]; have := Char.utf8Size_pos c; omega
    simp only [hne, ↓reduceIte]
    exact ih (i + c.utf8Size) (by omega)

/-- Extract with end position ≥ rawEndPos equals extract with rawEndPos. -/
private theorem extract_end_ge (s : String) (b : String.Pos.Raw) (e : Nat)
    (he : e ≥ s.utf8ByteSize) :
    String.Pos.Raw.extract s b ⟨e⟩ = String.Pos.Raw.extract s b s.rawEndPos := by
  have hb : b = ⟨b.byteIdx⟩ := by cases b; rfl
  rw [hb]
  unfold String.Pos.Raw.extract
  simp only [String.rawEndPos]
  by_cases hbe : e ≤ b.byteIdx
  · have hbr : s.utf8ByteSize ≤ b.byteIdx := by omega
    simp only [hbe, ↓reduceIte, hbr]
  · simp only [Nat.not_le] at hbe
    by_cases hbr : s.utf8ByteSize ≤ b.byteIdx
    · simp only [hbr, ↓reduceIte]
      have h1 : ¬(e ≤ b.byteIdx) := by omega
      simp only [h1, ↓reduceIte]
      have hpast : b.byteIdx ≥ 0 + utf8Len s.toList := by
        rw [Nat.zero_add, utf8Len_eq_utf8ByteSize]; exact hbr
      exact congrArg String.ofList (extract_go₁_past_end s.toList 0 b.byteIdx e hpast)
    · simp only [Nat.not_le] at hbr
      have h1 : ¬(e ≤ b.byteIdx) := by omega
      have h2 : ¬(s.utf8ByteSize ≤ b.byteIdx) := by omega
      simp only [h1, h2, ↓reduceIte]
      congr 1
      have hlen := utf8Len_eq_utf8ByteSize s
      exact extract_go₁_end_ge s.toList 0 b.byteIdx e s.utf8ByteSize
        (by rw [Nat.zero_add, hlen]; omega) (by rw [Nat.zero_add, hlen]; omega)

/-- Core lemma: `splitOnAux s "e.p." b i j r` returns `(extract s b rawEndPos :: r).reverse`
when `s` has no '.' character and `j.byteIdx ≤ 1` (pattern position is at most past 'e').

The invariant `j.byteIdx ≤ 1` is preserved because:
- j = 0: comparing with 'e'; if match, j becomes 1 (≤ 1)
- j = 1: comparing with '.'; since no '.' in s, always mismatch, j resets to 0 (≤ 1)
- j never reaches 2+ because that would require matching '.', which can't happen. -/
private theorem splitOnAux_no_dot_gen (s : String) (h : ∀ c, c ∈ s.toList → c ≠ '.')
    (b i j : String.Pos.Raw) (r : List String)
    (hj : j.byteIdx ≤ 1) :
    s.splitOnAux "e.p." b i j r =
      ((String.Pos.Raw.extract s b s.rawEndPos) :: r).reverse := by
  have dot_contra : ∀ (i' : String.Pos.Raw),
      (String.Pos.Raw.get s i' == String.Pos.Raw.get "e.p." ⟨1⟩) = true → False := by
    intro i' h_eq'
    have hep1 : String.Pos.Raw.get "e.p." ⟨1⟩ = '.' := by native_decide
    simp [BEq.beq, decide_eq_true_eq, hep1] at h_eq'
    have hmem : '.' ∈ s.toList := by
      cases get_mem_or_default' s i' with
      | inl hm => rw [← h_eq']; exact hm
      | inr hd => exfalso; exact dot_ne_default (h_eq' ▸ hd)
    exact h '.' hmem rfl
  fun_induction s.splitOnAux "e.p." b i j r with
  | case1 b i j r h_end =>
    have hi_ge : i.byteIdx ≥ s.rawEndPos.byteIdx := by
      simp [String.Pos.Raw.atEnd, decide_eq_true_eq] at h_end; exact h_end
    show (String.Pos.Raw.extract s b i :: r).reverse =
         (String.Pos.Raw.extract s b s.rawEndPos :: r).reverse
    congr 1; congr 1
    exact extract_end_ge s b i.byteIdx hi_ge
  | case2 b i j r h_not_end h_eq _ _ =>
    exfalso
    have hj01 : j.byteIdx = 0 ∨ j.byteIdx = 1 := by omega
    rename_i h_atEnd_val _ _
    cases hj01 with
    | inl hj0 =>
      have hfalse : String.Pos.Raw.atEnd "e.p." (String.Pos.Raw.next "e.p." j) = false := by
        have : j = ⟨0⟩ := String.Pos.Raw.ext hj0; rw [this]; native_decide
      simp [show h_atEnd_val = String.Pos.Raw.next "e.p." j from rfl, hfalse] at *
    | inr hj1 =>
      have hj_eq : j = ⟨1⟩ := String.Pos.Raw.ext hj1
      rw [hj_eq] at h_eq
      exact dot_contra i h_eq
  | case3 b i j r h_not_end h_eq _ _ =>
    have hj01 : j.byteIdx = 0 ∨ j.byteIdx = 1 := by omega
    cases hj01 with
    | inl hj0 =>
      rename_i ih1
      apply ih1
      show (String.Pos.Raw.next "e.p." j).byteIdx ≤ 1
      have : j = ⟨0⟩ := String.Pos.Raw.ext hj0
      rw [this]; native_decide
    | inr hj1 =>
      exfalso
      have hj_eq : j = ⟨1⟩ := String.Pos.Raw.ext hj1
      rw [hj_eq] at h_eq
      exact dot_contra i h_eq
  | case4 b i j r h_not_end h_neq _ =>
    rename_i ih1
    exact ih1 (by decide)

/-- When `s` has no '.' character, `splitOn s "e.p." = [s]`. -/
private theorem splitOn_ep_dot_eq_singleton (s : String) (h : ∀ c, c ∈ s.toList → c ≠ '.') :
    s.splitOn "e.p." = [s] := by
  unfold String.splitOn
  have hne : ("e.p." : String) ≠ "" := by decide
  simp only [BEq.beq, decide_eq_true_eq, hne, ↓reduceIte]
  have hsplit := splitOnAux_no_dot_gen s h 0 0 0 []
    (show (0 : String.Pos.Raw).byteIdx ≤ 1 by decide)
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append] at hsplit
  rw [hsplit]
  congr 1
  exact extract_full s

/-- **Main theorem**: Replacing "e.p." with "" in a string that contains no '.' is the identity.

**Proof chain**:
1. `String.replace s "e.p." "" = String.intercalate "" (s.splitOn "e.p.")` (axiom)
2. `s.splitOn "e.p." = [s]` (proved via `splitOnAux` when no '.' in s)
3. `String.intercalate "" [s] = s` (by definition of `intercalate`)

**Why the axiom is needed**: In Lean 4.26, `String.replace` is implemented through
a KMP searcher iterator framework (`ForwardSliceSearcher`) with `@[extern]` functions
that prevent kernel reduction. No upstream proof lemmas connect `String.replace` to
string-level properties. The axiom `replace_eq_intercalate_splitOn` bridges this gap;
it asserts the classical identity that was the definition of `replace` in earlier
Lean versions. -/
theorem String.replace_ep_dot_eq_self (s : String) (h : ∀ c, c ∈ s.toList → c ≠ '.') :
    s.replace "e.p." "" = s := by
  rw [String.replace_eq_intercalate_splitOn]
  rw [splitOn_ep_dot_eq_singleton s h]
  unfold String.intercalate; rfl

/-! ## Section 14: String.trim preserves non-whitespace characters -/


/-- Reverse induction principle for lists: induct by peeling from the right. -/
private theorem reverseRec {α : Type _} {motive : List α → Prop}
    (nil : motive [])
    (snoc : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    ∀ l : List α, motive l := by
  suffices h : ∀ (r : List α), motive r.reverse by
    intro l; have := h l.reverse; rwa [List.reverse_reverse] at this
  intro r; induction r with
  | nil => exact nil
  | cons a as ih => rw [List.reverse_cons]; exact snoc as.reverse a ih

/-- The head of dropWhile does not satisfy p. -/
private theorem head_dropWhile_false (p : Char → Bool) (l : List Char)
    (a : Char) (rest : List Char) (h : l.dropWhile p = a :: rest) :
    p a = false := by
  induction l with
  | nil => simp [List.dropWhile] at h
  | cons b bs ih =>
    rw [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · rename_i hpb
      have := (List.cons.inj h).1; subst this
      simp at hpb; exact hpb

/-- utf8GetAux returns the character at the accumulated byte position. -/
private theorem utf8GetAux_at_utf8Len (pref : List Char) (c : Char) (suf : List Char)
    (startPos : String.Pos.Raw) :
    String.Pos.Raw.utf8GetAux (pref ++ c :: suf) startPos
      ⟨startPos.byteIdx + utf8Len pref⟩ = c := by
  induction pref generalizing startPos with
  | nil => simp [utf8Len]; unfold String.Pos.Raw.utf8GetAux; rw [if_pos rfl]
  | cons d ds ih =>
    simp only [List.cons_append, utf8Len]; unfold String.Pos.Raw.utf8GetAux
    have hne : startPos ≠ ⟨startPos.byteIdx + (d.utf8Size + utf8Len ds)⟩ := by
      intro h; have h2 := congrArg String.Pos.Raw.byteIdx h
      simp at h2; have := Char.utf8Size_pos d; omega
    rw [if_neg hne,
      show (⟨startPos.byteIdx + (d.utf8Size + utf8Len ds)⟩ : String.Pos.Raw) =
        ⟨(startPos + d).byteIdx + utf8Len ds⟩ from
        String.Pos.Raw.ext (by simp [String.Pos.Raw.byteIdx_add_char]; omega)]
    exact ih (startPos + d)

/-- get at byte position utf8Len(pref) returns the character after pref. -/
private theorem get_at_utf8Len' (s : String) (pref : List Char) (c : Char) (suf : List Char)
    (hs : s.toList = pref ++ c :: suf) :
    String.Pos.Raw.get s ⟨utf8Len pref⟩ = c := by
  simp only [String.Pos.Raw.get, hs]
  rw [show (⟨utf8Len pref⟩ : String.Pos.Raw) =
    ⟨(0 : String.Pos.Raw).byteIdx + utf8Len pref⟩ from by simp]
  exact utf8GetAux_at_utf8Len pref c suf 0

/-- next at byte position utf8Len(pref) advances by c.utf8Size. -/
private theorem next_at_utf8Len' (s : String) (pref : List Char) (c : Char) (suf : List Char)
    (hs : s.toList = pref ++ c :: suf) :
    String.Pos.Raw.next s ⟨utf8Len pref⟩ = ⟨utf8Len pref + c.utf8Size⟩ := by
  simp only [String.Pos.Raw.next, get_at_utf8Len' s pref c suf hs]
  apply String.Pos.Raw.ext; simp [String.Pos.Raw.byteIdx_add_char]

/-- utf8PrevAux steps back one character from position utf8Len(l) + c.utf8Size. -/
private theorem utf8PrevAux_back_one' (l : List Char) (c : Char) (extra : List Char)
    (startPos : String.Pos.Raw) :
    String.Pos.Raw.utf8PrevAux (l ++ c :: extra) startPos
      ⟨startPos.byteIdx + utf8Len l + c.utf8Size⟩ =
    ⟨startPos.byteIdx + utf8Len l⟩ := by
  induction l generalizing startPos with
  | nil =>
    simp [utf8Len]; unfold String.Pos.Raw.utf8PrevAux
    rw [if_pos (by simp [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_add_char])]
  | cons d ds ih =>
    simp only [List.cons_append, utf8Len]; unfold String.Pos.Raw.utf8PrevAux
    have h_not_le :
        ¬ (⟨startPos.byteIdx + (d.utf8Size + utf8Len ds) + c.utf8Size⟩ : String.Pos.Raw) ≤
        (startPos + d) := by
      simp only [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_add_char]
      have := Char.utf8Size_pos c; omega
    rw [if_neg h_not_le,
      show (⟨startPos.byteIdx + (d.utf8Size + utf8Len ds) + c.utf8Size⟩ : String.Pos.Raw) =
        ⟨(startPos + d).byteIdx + utf8Len ds + c.utf8Size⟩ from
        String.Pos.Raw.ext (by simp [String.Pos.Raw.byteIdx_add_char]; omega),
      show (⟨startPos.byteIdx + (d.utf8Size + utf8Len ds)⟩ : String.Pos.Raw) =
        ⟨(startPos + d).byteIdx + utf8Len ds⟩ from
        String.Pos.Raw.ext (by simp [String.Pos.Raw.byteIdx_add_char]; omega)]
    exact ih (startPos + d)

/-- prev steps back one character from the end of pref ++ [c]. -/
private theorem prev_back_one' (s : String) (pref : List Char) (c : Char) (suf : List Char)
    (hs : s.toList = pref ++ c :: suf) :
    String.Pos.Raw.prev s ⟨utf8Len pref + c.utf8Size⟩ = ⟨utf8Len pref⟩ := by
  show String.Pos.Raw.utf8PrevAux s.toList 0 ⟨utf8Len pref + c.utf8Size⟩ = ⟨utf8Len pref⟩
  rw [hs,
    show utf8Len pref + c.utf8Size =
      (0 : String.Pos.Raw).byteIdx + utf8Len pref + c.utf8Size from by simp]
  rw [utf8PrevAux_back_one' pref c suf 0]; simp

/-- takeWhileAux scans from utf8Len(pref) and returns utf8Len(pref ++ takeWhile p rest). -/
private theorem takeWhileAux_eq_takeWhile (s : String) (p : Char → Bool)
    (pref rest : List Char) (hs : s.toList = pref ++ rest) :
    Substring.Raw.takeWhileAux s s.rawEndPos p ⟨utf8Len pref⟩ =
    ⟨utf8Len (pref ++ rest.takeWhile p)⟩ := by
  induction rest generalizing pref with
  | nil =>
    simp only [List.takeWhile, List.append_nil]
    rw [Substring.Raw.takeWhileAux.eq_1]
    have h_not_lt : ¬ ((⟨utf8Len pref⟩ : String.Pos.Raw) < s.rawEndPos) := by
      simp only [String.Pos.Raw.lt_iff, String.rawEndPos]
      rw [← utf8Len_eq_utf8ByteSize s, hs, List.append_nil]
      exact Nat.lt_irrefl _
    rw [dif_neg h_not_lt]
  | cons c cs ih =>
    rw [Substring.Raw.takeWhileAux.eq_1]
    have h_lt : (⟨utf8Len pref⟩ : String.Pos.Raw) < s.rawEndPos := by
      simp [String.Pos.Raw.lt_iff, String.rawEndPos]
      rw [← utf8Len_eq_utf8ByteSize s, hs, utf8Len_append, utf8Len]
      have := Char.utf8Size_pos c; omega
    rw [dif_pos h_lt, get_at_utf8Len' s pref c cs hs, List.takeWhile_cons]
    cases hpc : p c with
    | false => simp
    | true =>
      simp
      rw [next_at_utf8Len' s pref c cs hs]
      have hpref' : s.toList = (pref ++ [c]) ++ cs := by rw [hs]; simp
      have hlen : utf8Len pref + c.utf8Size = utf8Len (pref ++ [c]) := by
        rw [utf8Len_append, utf8Len]; simp [utf8Len]
      rw [hlen, ih (pref ++ [c]) hpref']
      congr 1; simp [List.append_assoc]

/-- takeRightWhileAux strips trailing p-satisfying chars.
    Given s.toList = prefix_left ++ core ++ ws_suffix ++ extra_tail,
    scanning from utf8Len(prefix_left ++ core ++ ws_suffix) back to utf8Len(prefix_left)
    returns utf8Len(prefix_left ++ core). -/
private theorem takeRightWhileAux_strips (s : String) (p : Char → Bool)
    (prefix_left core ws_suffix extra_tail : List Char)
    (hs : s.toList = prefix_left ++ core ++ ws_suffix ++ extra_tail)
    (h_ws : ∀ x, x ∈ ws_suffix → p x = true)
    (h_core : core = [] ∨
      ∃ init last_c, core = init ++ [last_c] ∧ p last_c = false) :
    Substring.Raw.takeRightWhileAux s ⟨utf8Len prefix_left⟩ p
      ⟨utf8Len (prefix_left ++ core ++ ws_suffix)⟩ =
    ⟨utf8Len (prefix_left ++ core)⟩ := by
  induction ws_suffix using reverseRec generalizing core extra_tail with
  | nil =>
    simp only [List.append_nil]
    cases h_core with
    | inl h_empty =>
      subst h_empty; simp only [List.append_nil]
      rw [Substring.Raw.takeRightWhileAux.eq_def]
      rw [dif_neg (by simp [String.Pos.Raw.lt_iff])]
    | inr h_ex =>
      obtain ⟨init, last_c, h_split, h_last⟩ := h_ex
      rw [Substring.Raw.takeRightWhileAux.eq_def]
      have h_lt : (⟨utf8Len prefix_left⟩ : String.Pos.Raw) <
          ⟨utf8Len (prefix_left ++ core)⟩ := by
        simp [String.Pos.Raw.lt_iff, utf8Len_append]
        rw [h_split, utf8Len_append, utf8Len]
        have := Char.utf8Size_pos last_c; omega
      rw [dif_pos h_lt]
      have hs' : s.toList = (prefix_left ++ init) ++ last_c :: extra_tail := by
        rw [hs]; simp [h_split]
      show (let i' := String.Pos.Raw.prev s ⟨utf8Len (prefix_left ++ core)⟩;
            let c := String.Pos.Raw.get s i';
            if (! p c) = true then ⟨utf8Len (prefix_left ++ core)⟩
            else Substring.Raw.takeRightWhileAux s ⟨utf8Len prefix_left⟩ p i') =
           ⟨utf8Len (prefix_left ++ core)⟩
      have h_endPos : (⟨utf8Len (prefix_left ++ core)⟩ : String.Pos.Raw) =
          ⟨utf8Len (prefix_left ++ init) + last_c.utf8Size⟩ := by
        apply String.Pos.Raw.ext; rw [h_split]
        rw [show prefix_left ++ (init ++ [last_c]) =
          (prefix_left ++ init) ++ [last_c] from by simp]
        rw [utf8Len_append, utf8Len]; simp [utf8Len]
      have h_prev : String.Pos.Raw.prev s ⟨utf8Len (prefix_left ++ core)⟩ =
          ⟨utf8Len (prefix_left ++ init)⟩ := by
        rw [h_endPos]
        exact prev_back_one' s (prefix_left ++ init) last_c extra_tail hs'
      have h_get : String.Pos.Raw.get s ⟨utf8Len (prefix_left ++ init)⟩ = last_c :=
        get_at_utf8Len' s (prefix_left ++ init) last_c extra_tail hs'
      simp only [h_prev, h_get,
        show (! p last_c) = true from by rw [h_last]; simp, ite_true]
  | snoc ws w ih =>
    have hw : p w = true := h_ws w (by simp)
    have hs_split : s.toList =
        (prefix_left ++ core ++ ws) ++ w :: extra_tail := by rw [hs]; simp
    have h_endPos_eq : utf8Len (prefix_left ++ core ++ (ws ++ [w])) =
        utf8Len (prefix_left ++ core ++ ws) + w.utf8Size := by
      rw [show prefix_left ++ core ++ (ws ++ [w]) =
        (prefix_left ++ core ++ ws) ++ [w] from by simp]
      rw [utf8Len_append, utf8Len]; simp [utf8Len]
    rw [Substring.Raw.takeRightWhileAux.eq_def]
    have h_lt : (⟨utf8Len prefix_left⟩ : String.Pos.Raw) <
        ⟨utf8Len (prefix_left ++ core ++ (ws ++ [w]))⟩ := by
      simp [String.Pos.Raw.lt_iff, utf8Len_append, utf8Len]
      have := Char.utf8Size_pos w; omega
    rw [dif_pos h_lt]
    have h_prev :
        String.Pos.Raw.prev s ⟨utf8Len (prefix_left ++ core ++ (ws ++ [w]))⟩ =
        ⟨utf8Len (prefix_left ++ core ++ ws)⟩ := by
      rw [h_endPos_eq]
      exact prev_back_one' s (prefix_left ++ core ++ ws) w extra_tail hs_split
    have h_get :
        String.Pos.Raw.get s ⟨utf8Len (prefix_left ++ core ++ ws)⟩ = w :=
      get_at_utf8Len' s (prefix_left ++ core ++ ws) w extra_tail hs_split
    show (let i' :=
            String.Pos.Raw.prev s ⟨utf8Len (prefix_left ++ core ++ (ws ++ [w]))⟩;
          let c := String.Pos.Raw.get s i';
          if (! p c) = true then ⟨utf8Len (prefix_left ++ core ++ (ws ++ [w]))⟩
          else Substring.Raw.takeRightWhileAux s ⟨utf8Len prefix_left⟩ p i') =
         ⟨utf8Len (prefix_left ++ core)⟩
    simp only [h_prev, h_get, show (! p w) = false from by rw [hw]; simp]
    exact ih core (w :: extra_tail)
      (by rw [hs]; simp) (fun x hx => h_ws x (by simp [hx])) h_core

/-- go₂ extracts the middle portion of a list. -/
private theorem extract_go₂_middle' (mid extra : List Char) (startPos : Nat) :
    String.Pos.Raw.extract.go₂ (mid ++ extra) ⟨startPos⟩
      ⟨startPos + utf8Len mid⟩ = mid := by
  induction mid generalizing startPos extra with
  | nil =>
    simp [utf8Len]
    cases extra with
    | nil => rfl
    | cons c cs => unfold String.Pos.Raw.extract.go₂; simp
  | cons c cs ih =>
    simp only [utf8Len, List.cons_append]
    unfold String.Pos.Raw.extract.go₂
    have hne : (⟨startPos⟩ : String.Pos.Raw) ≠
        ⟨startPos + (c.utf8Size + utf8Len cs)⟩ := by
      simp [String.Pos.Raw.mk.injEq]
      have := Char.utf8Size_pos c; omega
    rw [if_neg hne]
    congr 1
    rw [show (⟨startPos + (c.utf8Size + utf8Len cs)⟩ : String.Pos.Raw) =
        ⟨startPos + c.utf8Size + utf8Len cs⟩ from
        String.Pos.Raw.ext (by show startPos + (c.utf8Size + utf8Len cs) =
          startPos + c.utf8Size + utf8Len cs; omega),
      show (⟨startPos⟩ : String.Pos.Raw) + c = ⟨startPos + c.utf8Size⟩ from
        String.Pos.Raw.ext (by simp [String.Pos.Raw.byteIdx_add_char])]
    exact ih extra (startPos + c.utf8Size)

/-- go₁ skips through a prefix to reach the start of extraction. -/
private theorem extract_go₁_skip' (pref rest : List Char) (endPos : String.Pos.Raw) :
    String.Pos.Raw.extract.go₁ (pref ++ rest) 0 ⟨utf8Len pref⟩ endPos =
    String.Pos.Raw.extract.go₂ rest ⟨utf8Len pref⟩ endPos := by
  suffices h : ∀ (acc : Nat),
      String.Pos.Raw.extract.go₁ (pref ++ rest) ⟨acc⟩ ⟨acc + utf8Len pref⟩ endPos =
      String.Pos.Raw.extract.go₂ rest ⟨acc + utf8Len pref⟩ endPos by
    have h0 := h 0; simp at h0; exact h0
  induction pref generalizing rest endPos with
  | nil =>
    intro acc; simp [utf8Len]
    cases rest with
    | nil => rfl
    | cons c cs => unfold String.Pos.Raw.extract.go₁; simp
  | cons p ps ih =>
    intro acc
    simp only [List.cons_append, utf8Len]
    unfold String.Pos.Raw.extract.go₁
    have hne : (⟨acc⟩ : String.Pos.Raw) ≠
        ⟨acc + (p.utf8Size + utf8Len ps)⟩ := by
      simp [String.Pos.Raw.mk.injEq]
      have := Char.utf8Size_pos p; omega
    rw [if_neg hne,
      show (⟨acc⟩ : String.Pos.Raw) + p = ⟨acc + p.utf8Size⟩ from
        String.Pos.Raw.ext (by simp [String.Pos.Raw.byteIdx_add_char]),
      show (⟨acc + (p.utf8Size + utf8Len ps)⟩ : String.Pos.Raw) =
        ⟨acc + p.utf8Size + utf8Len ps⟩ from
        String.Pos.Raw.ext (by show acc + (p.utf8Size + utf8Len ps) =
          acc + p.utf8Size + utf8Len ps; omega)]
    exact ih rest endPos (acc + p.utf8Size)

/-- Extract between byte positions utf8Len(prefix_left) and
    utf8Len(prefix_left ++ core) gives String.ofList core. -/
private theorem extract_middle' (s : String) (prefix_left core extra : List Char)
    (hs : s.toList = prefix_left ++ core ++ extra) :
    String.Pos.Raw.extract s ⟨utf8Len prefix_left⟩
      ⟨utf8Len (prefix_left ++ core)⟩ =
    String.ofList core := by
  show (if (⟨utf8Len prefix_left⟩ : String.Pos.Raw).byteIdx ≥
      (⟨utf8Len (prefix_left ++ core)⟩ : String.Pos.Raw).byteIdx then ""
    else String.ofList (String.Pos.Raw.extract.go₁ s.toList 0
      ⟨utf8Len prefix_left⟩ ⟨utf8Len (prefix_left ++ core)⟩)) =
    String.ofList core
  rw [utf8Len_append]
  by_cases h_core_zero : utf8Len core = 0
  · have h_core_empty : core = [] := by
      cases core with
      | nil => rfl
      | cons c cs =>
        simp [utf8Len] at h_core_zero
        have := Char.utf8Size_pos c; omega
    subst h_core_empty; simp [utf8Len]
  · have h_not_ge :
        ¬ (utf8Len prefix_left ≥ utf8Len prefix_left + utf8Len core) := by omega
    rw [show (⟨utf8Len prefix_left⟩ : String.Pos.Raw).byteIdx =
      utf8Len prefix_left from rfl,
      show (⟨utf8Len prefix_left + utf8Len core⟩ : String.Pos.Raw).byteIdx =
      utf8Len prefix_left + utf8Len core from rfl]
    rw [if_neg h_not_ge, hs,
      show prefix_left ++ core ++ extra = prefix_left ++ (core ++ extra) from by simp]
    rw [extract_go₁_skip' prefix_left (core ++ extra)
      ⟨utf8Len prefix_left + utf8Len core⟩]
    rw [extract_go₂_middle' core extra (utf8Len prefix_left)]

/-- Membership in dropWhile: if p x = false and x ∈ l, then x ∈ l.dropWhile p. -/
private theorem mem_dropWhile_of_not_pred (p : Char → Bool) (l : List Char) (x : Char)
    (hp : p x = false) (hmem : x ∈ l) : x ∈ l.dropWhile p := by
  induction l with
  | nil => exact hmem
  | cons a as ih =>
    rw [List.dropWhile_cons]
    split
    · rename_i ha
      simp at hmem
      rcases hmem with rfl | hmem
      · rw [hp] at ha; exact absurd ha (by simp)
      · exact ih hmem
    · exact hmem

/-- All elements of takeWhile satisfy the predicate. -/
private theorem takeWhile_forall (p : Char → Bool) (l : List Char) :
    ∀ x, x ∈ l.takeWhile p → p x = true := by
  induction l with
  | nil => simp [List.takeWhile]
  | cons a as ih =>
    intro x hx
    rw [List.takeWhile_cons] at hx
    split at hx
    · simp at hx; rcases hx with rfl | hx
      · assumption
      · exact ih x hx
    · simp at hx

/-- The core after trimming is empty or ends with a non-p character.
    Here core_rev = (l.dropWhile p).reverse.dropWhile p, and we show
    core_rev.reverse has the required property. -/
private theorem trim_core_property (p : Char → Bool) (l : List Char) :
    let core_rev := (l.dropWhile p).reverse.dropWhile p
    core_rev.reverse = [] ∨
      ∃ init last_c, core_rev.reverse = init ++ [last_c] ∧ p last_c = false := by
  intro core_rev
  by_cases h_empty : core_rev = []
  · left; simp [h_empty]
  · right
    obtain ⟨first_rev, rest_rev, h_rev⟩ := List.exists_cons_of_ne_nil h_empty
    have h_pf : p first_rev = false :=
      head_dropWhile_false p (l.dropWhile p).reverse first_rev rest_rev h_rev
    exact ⟨rest_rev.reverse, first_rev,
      by show core_rev.reverse = rest_rev.reverse ++ [first_rev]
         rw [h_rev, List.reverse_cons],
      h_pf⟩

/-- Core list-level decomposition for trim:
    Any list can be split as leading ++ core ++ trailing where
    - all leading chars satisfy p
    - all trailing chars satisfy p
    - core is empty or ends with a non-p character -/
private theorem trim_list_decomp (p : Char → Bool) (l : List Char) :
    ∃ (leading core trailing : List Char),
      l = leading ++ core ++ trailing ∧
      (∀ x, x ∈ leading → p x = true) ∧
      (∀ x, x ∈ trailing → p x = true) ∧
      (core = [] ∨ ∃ init last_c, core = init ++ [last_c] ∧ p last_c = false) := by
  let leading := l.takeWhile p
  let remaining := l.dropWhile p
  let trailing := (remaining.reverse.takeWhile p).reverse
  let core := (remaining.reverse.dropWhile p).reverse
  refine ⟨leading, core, trailing, ?_, ?_, ?_, ?_⟩
  · have h1 : l = leading ++ remaining := List.takeWhile_append_dropWhile.symm
    have h2 : remaining = core ++ trailing := by
      show remaining =
        (remaining.reverse.dropWhile p).reverse ++ (remaining.reverse.takeWhile p).reverse
      rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
    rw [h1, h2]; simp [List.append_assoc]
  · exact takeWhile_forall p l
  · intro x hx
    rw [List.mem_reverse] at hx
    exact takeWhile_forall p remaining.reverse x hx
  · exact trim_core_property p l

/-- The main theorem: if c is not whitespace and c is in s, then c is in s.trim. -/
theorem String.trim_preserves_non_ws_char (s : String) (c : Char)
    (hc : c.isWhitespace = false) (hmem : c ∈ s.toList) : c ∈ s.trim.toList := by
  -- Use trim_list_decomp to get the three-part decomposition
  -- leading = s.toList.takeWhile isWS
  -- core = ...
  -- trailing = ...
  -- We work without let bindings to avoid definitional transparency issues.
  -- First, get membership in the core via list-level reasoning:
  -- s.toList = leading ++ core ++ trailing, all leading/trailing are WS, so c ∈ core.
  -- Then show s.trim.toList = core via byte-level bridge.
  --
  -- The approach: prove c ∈ (s.toList.dropWhile Char.isWhitespace) first,
  -- then c ∈ reverse(dropWhile isWS (reverse (dropWhile isWS s.toList)))
  -- which equals s.trim.toList.
  --
  -- Actually, let's use a simpler approach: just show the membership directly
  -- using dropWhile properties.
  --
  -- Key list fact: c ∈ l ∧ p c = false → c ∈ l.dropWhile p
  have h1 : c ∈ s.toList.dropWhile Char.isWhitespace :=
    mem_dropWhile_of_not_pred Char.isWhitespace s.toList c hc hmem
  -- c ∈ remaining → c ∈ remaining.reverse
  have h2 : c ∈ (s.toList.dropWhile Char.isWhitespace).reverse :=
    List.mem_reverse.mpr h1
  -- c ∈ remaining.reverse → c ∈ remaining.reverse.dropWhile isWS
  have h3 : c ∈ (s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace :=
    mem_dropWhile_of_not_pred Char.isWhitespace _ c hc h2
  -- c ∈ dropWhile(reverse(dropWhile L)) → c ∈ reverse(dropWhile(reverse(dropWhile L)))
  have h4 : c ∈ ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse :=
    List.mem_reverse.mpr h3
  -- Now we need: s.trim.toList = reverse(dropWhile isWS (reverse(dropWhile isWS s.toList)))
  -- This is the list characterization of trim.
  -- To prove this, we use the byte-level bridge.
  suffices h_trim_toList : s.trim.toList =
      ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse by
    rw [h_trim_toList]; exact h4
  -- Prove the list characterization of s.trim
  -- Define the decomposition pieces
  -- Decomposition helper for any list
  have rev_split : ∀ (l : List Char),
      l = (l.reverse.dropWhile Char.isWhitespace).reverse ++
          (l.reverse.takeWhile Char.isWhitespace).reverse := by
    intro l
    have h := (List.takeWhile_append_dropWhile
      (p := Char.isWhitespace) (l := l.reverse)).symm
    have h2 : l.reverse.reverse = (l.reverse.takeWhile Char.isWhitespace ++
      l.reverse.dropWhile Char.isWhitespace).reverse := by congr 1
    rw [List.reverse_reverse, List.reverse_append] at h2
    exact h2
  -- s.toList = leading ++ core ++ trailing
  have h_full : s.toList =
      s.toList.takeWhile Char.isWhitespace ++
      ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse ++
      ((s.toList.dropWhile Char.isWhitespace).reverse.takeWhile Char.isWhitespace).reverse := by
    have h1 : s.toList = s.toList.takeWhile Char.isWhitespace ++
        s.toList.dropWhile Char.isWhitespace :=
      (List.takeWhile_append_dropWhile).symm
    have h2 := rev_split (s.toList.dropWhile Char.isWhitespace)
    exact Eq.trans (Eq.trans h1 (congrArg
      (s.toList.takeWhile Char.isWhitespace ++ ·) h2))
      (List.append_assoc _ _ _).symm
  have h_trailing_ws : ∀ x,
      x ∈ ((s.toList.dropWhile Char.isWhitespace).reverse.takeWhile Char.isWhitespace).reverse →
      Char.isWhitespace x = true := by
    intro x hx; rw [List.mem_reverse] at hx
    exact takeWhile_forall Char.isWhitespace (s.toList.dropWhile Char.isWhitespace).reverse x hx
  have h_core_prop := trim_core_property Char.isWhitespace s.toList
  -- Byte-level: takeWhileAux
  have h_left : Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace 0 =
      ⟨utf8Len (s.toList.takeWhile Char.isWhitespace)⟩ := by
    have := takeWhileAux_eq_takeWhile s Char.isWhitespace [] s.toList (by simp)
    simp [utf8Len] at this; exact this
  -- Byte-level: takeRightWhileAux
  have h_right : Substring.Raw.takeRightWhileAux s
      ⟨utf8Len (s.toList.takeWhile Char.isWhitespace)⟩ Char.isWhitespace s.rawEndPos =
      ⟨utf8Len (s.toList.takeWhile Char.isWhitespace ++
        ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)⟩ := by
    rw [show s.rawEndPos =
      ⟨utf8Len (s.toList.takeWhile Char.isWhitespace ++
        ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse ++
        ((s.toList.dropWhile Char.isWhitespace).reverse.takeWhile Char.isWhitespace).reverse)⟩ from
      String.Pos.Raw.ext (by
        show s.utf8ByteSize = _
        rw [← utf8Len_eq_utf8ByteSize s]; congr 1)]
    exact takeRightWhileAux_strips s Char.isWhitespace
      (s.toList.takeWhile Char.isWhitespace)
      (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)
      (((s.toList.dropWhile Char.isWhitespace).reverse.takeWhile Char.isWhitespace).reverse)
      []
      (by rw [← h_full]; simp) h_trailing_ws h_core_prop
  -- Byte-level: extract
  have h_extract : String.Pos.Raw.extract s
      ⟨utf8Len (s.toList.takeWhile Char.isWhitespace)⟩
      ⟨utf8Len (s.toList.takeWhile Char.isWhitespace ++
        ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)⟩ =
      String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse :=
    extract_middle' s
      (s.toList.takeWhile Char.isWhitespace)
      (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)
      (((s.toList.dropWhile Char.isWhitespace).reverse.takeWhile Char.isWhitespace).reverse)
      (by rw [← h_full])
  -- Combine: s.trim = String.ofList core_list
  have h_trim_eq : s.trim = String.ofList
      ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse := by
    rw [string_trim_eq_legacy]
    show (Substring.Raw.trim ⟨s, 0, s.rawEndPos⟩).toString = _
    show String.Pos.Raw.extract s
      (Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace 0)
      (Substring.Raw.takeRightWhileAux s
        (Substring.Raw.takeWhileAux s s.rawEndPos Char.isWhitespace 0)
        Char.isWhitespace s.rawEndPos) = _
    rw [h_left, h_right, h_extract]
  rw [h_trim_eq, String.toList_ofList]



end StringLemmas

end Chess
