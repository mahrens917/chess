/-
StringLemmas.lean

This file provides foundational string manipulation lemmas needed for proving
SAN (Standard Algebraic Notation) parsing properties.

Built on top of Lean 4.26's standard library String lemmas.

Includes infrastructure lemmas connecting byte-level string operations to
character-level semantics for dropRight and endsWith proofs.
-/

namespace Chess

namespace StringLemmas

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

/-- dropRight 0 is the identity function -/
private theorem dropRight_zero (s : String) : s.dropRight 0 = s := by
  unfold String.dropRight
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
  -- Base case: t is empty
  by_cases ht : t = ""
  · rw [ht]
    simp only [String.append_empty, String.length_empty]
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
    unfold String.dropRight
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

end StringLemmas

end Chess
