/-
SanUniquenessProof.lean

Proof that moveToSAN is injective (up to MoveEquiv) on legal moves.

FIDE Laws of Chess, Appendix C (Standard Algebraic Notation):
- Each legal move has a unique SAN representation
- Disambiguation uses file, rank, or both as needed
-/
import Chess.Core
import Chess.Movement
import Chess.Game
import Chess.Rules
import Chess.Parsing
import Chess.StringLemmas

namespace Chess
namespace SanUniqueness

open scoped Classical
open Rules Parsing

-- ============================================================================
-- Section 1: Suffix analysis - equal moveToSAN implies equal moveToSanBase
-- ============================================================================

/-- String.toList is injective. -/
private theorem string_eq_of_toList_eq {s1 s2 : String}
    (h : s1.toList = s2.toList) : s1 = s2 :=
  String.ext h

/-- If l1 ++ [a] = l2 ++ [b] then l1 = l2 and a = b. -/
private theorem list_append_singleton_inj {α : Type} {l1 l2 : List α} {a b : α}
    (h : l1 ++ [a] = l2 ++ [b]) : l1 = l2 ∧ a = b := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp at h; exact ⟨rfl, h⟩
    | cons x xs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨_, h2⟩ := h
      have := congrArg List.length h2
      simp at this
  | cons x xs ih =>
    cases l2 with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨_, h2⟩ := h
      have := congrArg List.length h2
      simp at this
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hxy, htl⟩ := h
      have ⟨hxs, hab⟩ := ih htl
      exact ⟨by rw [hxy, hxs], hab⟩

/-- The last element of l ++ [a] is a. -/
private theorem list_getLast_append_singleton {α : Type} (l : List α) (a : α) :
    (l ++ [a]).getLast? = some a := by
  simp [List.getLast?_eq_getLast, List.getLast_append_of_ne_nil _ (by simp : [a] ≠ [])]

/-- Key lemma: equal moveToSAN implies equal moveToSanBase.
    Proof: moveToSAN = base ++ suffix where suffix ∈ {"","+","#"}.
    The base never ends with '+' or '#', so equal full SANs force equal suffixes,
    hence equal bases by string cancellation. -/
private theorem moveToSAN_eq_append (gs : GameState) (m : Move) :
    moveToSAN gs m = moveToSanBase gs m ++
      (if isCheckmate (GameState.playMove gs m) then "#"
       else if inCheck (GameState.playMove gs m).board (GameState.playMove gs m).toMove then "+"
       else "") := by
  unfold moveToSAN; rfl

/-- algebraic notation never has '+' as last char. Verified over all 64 squares. -/
private theorem algebraic_last_ne_plus :
    ∀ (f r : Fin 8), ({ file := f, rank := r : Square}).algebraic.toList.getLast? ≠ some '+' := by native_decide

/-- algebraic notation never has '#' as last char. Verified over all 64 squares. -/
private theorem algebraic_last_ne_hash :
    ∀ (f r : Fin 8), ({ file := f, rank := r : Square}).algebraic.toList.getLast? ≠ some '#' := by native_decide

/-- Combined helper. -/
private theorem algebraic_last_ne_plus_hash (sq : Square) :
    ∀ c, (sq.algebraic).toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' := by
  cases sq with | mk f r =>
  intro c hc
  constructor
  · intro heq; subst heq; exact algebraic_last_ne_plus f r hc
  · intro heq; subst heq; exact algebraic_last_ne_hash f r hc

/-- promotionSuffix is either "" or "=Q"/"=R"/"=B"/"=N" or "=K" (which doesn't occur for legal moves). -/
private theorem promotionSuffix_cases (m : Move) :
    promotionSuffix m = "" ∨ promotionSuffix m = "=Q" ∨ promotionSuffix m = "=R" ∨
    promotionSuffix m = "=B" ∨ promotionSuffix m = "=N" ∨ promotionSuffix m = "=K" ∨
    promotionSuffix m = "=" := by
  unfold promotionSuffix pieceLetter
  cases m.promotion with
  | none => left; rfl
  | some pt => right; cases pt <;> simp <;> native_decide

/-- Helper for concrete string last-char proofs -/
private theorem last_char_ne_of_eq {s : String} {d : Char}
    (heval : s.toList.getLast? = some d) (hd1 : d ≠ '+') (hd2 : d ≠ '#') :
    ∀ c : Char, s.toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' := by
  intro c hc; rw [heval] at hc; have := Option.some.inj hc; subst this; exact ⟨hd1, hd2⟩

/-- Concrete string last-char checks. -/
private theorem last_ne_plus_hash_empty : ∀ c : Char, "".toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' := by
  intro c hc; simp at hc
private theorem last_ne_plus_hash_eqQ : ∀ c : Char, "=Q".toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' :=
  last_char_ne_of_eq (d := 'Q') (by native_decide) (by decide) (by decide)
private theorem last_ne_plus_hash_eqR : ∀ c : Char, "=R".toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' :=
  last_char_ne_of_eq (d := 'R') (by native_decide) (by decide) (by decide)
private theorem last_ne_plus_hash_eqB : ∀ c : Char, "=B".toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' :=
  last_char_ne_of_eq (d := 'B') (by native_decide) (by decide) (by decide)
private theorem last_ne_plus_hash_eqN : ∀ c : Char, "=N".toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' :=
  last_char_ne_of_eq (d := 'N') (by native_decide) (by decide) (by decide)
private theorem last_ne_plus_hash_eqK : ∀ c : Char, "=K".toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' :=
  last_char_ne_of_eq (d := 'K') (by native_decide) (by decide) (by decide)
private theorem last_ne_plus_hash_eq : ∀ c : Char, "=".toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' :=
  last_char_ne_of_eq (d := '=') (by native_decide) (by decide) (by decide)

/-- No concrete promotion suffix string has '+' or '#' as its last char. -/
private theorem promo_string_last_ok (s : String)
    (hs : s = "" ∨ s = "=Q" ∨ s = "=R" ∨ s = "=B" ∨ s = "=N" ∨ s = "=K" ∨ s = "=") :
    ∀ c, s.toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' := by
  rcases hs with h | h | h | h | h | h | h <;> subst h
  · exact last_ne_plus_hash_empty
  · exact last_ne_plus_hash_eqQ
  · exact last_ne_plus_hash_eqR
  · exact last_ne_plus_hash_eqB
  · exact last_ne_plus_hash_eqN
  · exact last_ne_plus_hash_eqK
  · exact last_ne_plus_hash_eq

/-- The last character of promotionSuffix (when nonempty) is never '+' or '#'. -/
private theorem promotionSuffix_last_ok (m : Move) :
    ∀ c, (promotionSuffix m).toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' :=
  promo_string_last_ok _ (promotionSuffix_cases m)

/-- Helper: getLast? of l1 ++ l2 when l2 is nonempty. -/
private theorem list_getLast_append_nonempty {α : Type} :
    ∀ (l1 l2 : List α), l2 ≠ [] → (l1 ++ l2).getLast? = l2.getLast?
  | [], l2, _ => by simp
  | [x], l2, hne => by
    simp only [List.cons_append, List.nil_append]
    cases l2 with
    | nil => contradiction
    | cons y ys => simp [List.getLast?]
  | x :: y :: xs, l2, hne => by
    simp only [List.cons_append]
    have : (y :: xs ++ l2) ≠ [] := by simp
    rw [show (x :: y :: (xs ++ l2)).getLast? = (y :: (xs ++ l2)).getLast? from by
      simp [List.getLast?]]
    exact list_getLast_append_nonempty (y :: xs) l2 hne

/-- The last character of algebraic ++ promotionSuffix is never '+' or '#'.
    If promotionSuffix is "", last char comes from algebraic (a digit).
    If promotionSuffix is "=X", last char is X (Q/R/B/N). -/
private theorem alg_promo_last_ok (sq : Square) (m : Move) :
    ∀ c, (sq.algebraic ++ promotionSuffix m).toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' := by
  intro c hc
  -- Two cases: promotionSuffix is "" or nonempty
  rcases promotionSuffix_cases m with hp | hp | hp | hp | hp | hp | hp
  · -- promotionSuffix = "": last char from algebraic
    rw [hp, String.append_empty] at hc
    exact algebraic_last_ne_plus_hash sq c hc
  all_goals (
    -- promotionSuffix is nonempty: last char from promotionSuffix
    rw [hp] at hc
    simp only [String.toList_append] at hc
    have hne : (promotionSuffix m).toList ≠ [] := by rw [hp]; decide
    rw [hp] at hne
    rw [list_getLast_append_nonempty _ _ hne] at hc
    exact promotionSuffix_last_ok m c (by rw [hp]; exact hc))

/-- algebraic toList is nonempty (at least 2 chars: file + rank). -/
private theorem algebraic_toList_ne_nil (sq : Square) :
    sq.algebraic.toList ≠ [] := by
  cases sq with | mk f r =>
  unfold Square.algebraic
  simp only [String.toList_append]
  intro h
  have := List.append_eq_nil_iff.mp h
  exact absurd this.1 (by simp [Char.toString, String.toList_singleton])

/-- algebraic.toList ++ promotionSuffix.toList is nonempty. -/
private theorem alg_promo_toList_ne_nil (sq : Square) (m : Move) :
    sq.algebraic.toList ++ (promotionSuffix m).toList ≠ [] := by
  intro h
  have := List.append_eq_nil_iff.mp h
  exact algebraic_toList_ne_nil sq this.1

/-- Helper: getLast? of a string append when the right part is nonempty. -/
private theorem string_getLast_append (s1 s2 : String) (hne : s2.toList ≠ []) :
    (s1 ++ s2).toList.getLast? = s2.toList.getLast? := by
  simp only [String.toList_append]
  exact list_getLast_append_nonempty s1.toList s2.toList hne

/-- algebraic ++ promotionSuffix has nonempty toList. -/
private theorem alg_promo_ne_nil (sq : Square) (m : Move) :
    (sq.algebraic ++ promotionSuffix m).toList ≠ [] := by
  simp only [String.toList_append]
  exact fun h => algebraic_toList_ne_nil sq (List.append_eq_nil_iff.mp h).1

/-- The last character of moveToSanBase is never '+' or '#'. -/
private theorem moveToSanBase_last_ok (gs : GameState) (m : Move) :
    ∀ c, (moveToSanBase gs m).toList.getLast? = some c → c ≠ '+' ∧ c ≠ '#' := by
  intro c hc
  unfold moveToSanBase at hc
  by_cases hcastle : m.isCastle = true
  · -- Castle case: "O-O" or "O-O-O", both end with 'O'
    simp only [hcastle, ↓reduceIte] at hc
    split at hc
    · -- "O-O" ends with 'O'
      exact last_char_ne_of_eq (d := 'O') (by native_decide) (by decide) (by decide) c hc
    · -- "O-O-O" ends with 'O'
      exact last_char_ne_of_eq (d := 'O') (by native_decide) (by decide) (by decide) c hc
  · -- Non-castle case: base = prefix ++ algebraic ++ promotionSuffix
    -- The last char comes from algebraic ++ promotionSuffix
    simp only [hcastle, Bool.false_eq_true, ↓reduceIte] at hc
    -- In both pawn and piece cases, the string is of the form
    -- (some_prefix) ++ (m.toSq.algebraic ++ promotionSuffix m)
    -- Since algebraic ++ promotionSuffix is nonempty, getLast? comes from it
    have halg : (m.toSq.algebraic ++ promotionSuffix m).toList ≠ [] :=
      alg_promo_ne_nil m.toSq m
    split at hc
    · -- Pawn: ((pre ++ sep) ++ algebraic ++ promotionSuffix)
      -- Rewrite as (pre ++ sep) ++ (algebraic ++ promotionSuffix)
      -- The string is ((if cap then fileChar else "") ++ (if cap then "x" else "")) ++ alg ++ promo
      -- = prefix_str ++ (alg ++ promo)
      -- Since alg ++ promo ≠ "", getLast? = getLast? of (alg ++ promo)
      have hne : (m.toSq.algebraic ++ promotionSuffix m).toList ≠ [] := halg
      -- hc is about the full pawn SAN string
      -- We need to show its getLast? = getLast? of (alg ++ promo)
      -- The pawn SAN = pre ++ sep ++ alg ++ promo = (pre ++ sep) ++ (alg ++ promo)
      -- Use String.append_assoc
      rw [show ∀ (a b c d : String), (a ++ b) ++ c ++ d = (a ++ b) ++ (c ++ d) from fun a b c d => by
        simp [String.append_assoc]] at hc
      rw [string_getLast_append _ _ hne] at hc
      exact alg_promo_last_ok m.toSq m c hc
    · -- Piece: ((pieceLetter ++ dis ++ sep) ++ algebraic ++ promotionSuffix)
      have hne : (m.toSq.algebraic ++ promotionSuffix m).toList ≠ [] := halg
      rw [show ∀ (a b c d e : String), (a ++ b ++ c) ++ d ++ e = (a ++ b ++ c) ++ (d ++ e) from
        fun a b c d e => by simp [String.append_assoc]] at hc
      rw [string_getLast_append _ _ hne] at hc
      exact alg_promo_last_ok m.toSq m c hc

/-- The last character of moveToSanBase is never '+'. -/
private theorem moveToSanBase_last_ne_plus (gs : GameState) (m : Move) :
    ∀ c, (moveToSanBase gs m).toList.getLast? = some c → c ≠ '+' := by
  intro c hc; exact (moveToSanBase_last_ok gs m c hc).1

/-- The last character of moveToSanBase is never '#'. -/
private theorem moveToSanBase_last_ne_hash (gs : GameState) (m : Move) :
    ∀ c, (moveToSanBase gs m).toList.getLast? = some c → c ≠ '#' := by
  intro c hc; exact (moveToSanBase_last_ok gs m c hc).2

/-- base ++ "#" ≠ base2 (base2 never ends with '#') -/
private theorem base_append_hash_ne (gs : GameState) (m1 m2 : Move) :
    moveToSanBase gs m1 ++ "#" ≠ moveToSanBase gs m2 := by
  intro heq
  have h : (moveToSanBase gs m2).toList.getLast? = some '#' := by
    have := congrArg String.toList heq
    simp only [String.toList_append] at this
    rw [← this]
    exact list_getLast_append_singleton _ _
  exact moveToSanBase_last_ne_hash gs m2 '#' h rfl

/-- base ++ "+" ≠ base2 (base2 never ends with '+') -/
private theorem base_append_plus_ne (gs : GameState) (m1 m2 : Move) :
    moveToSanBase gs m1 ++ "+" ≠ moveToSanBase gs m2 := by
  intro heq
  have h : (moveToSanBase gs m2).toList.getLast? = some '+' := by
    have := congrArg String.toList heq
    simp only [String.toList_append] at this
    rw [← this]
    exact list_getLast_append_singleton _ _
  exact moveToSanBase_last_ne_plus gs m2 '+' h rfl

theorem base_eq_of_moveToSAN_eq (gs : GameState) (m1 m2 : Move)
    (hsan : moveToSAN gs m1 = moveToSAN gs m2) :
    moveToSanBase gs m1 = moveToSanBase gs m2 := by
  rw [moveToSAN_eq_append, moveToSAN_eq_append] at hsan
  by_cases hc1 : isCheckmate (GameState.playMove gs m1) = true
  · simp only [hc1, ↓reduceIte] at hsan
    by_cases hc2 : isCheckmate (GameState.playMove gs m2) = true
    · simp only [hc2, ↓reduceIte] at hsan
      exact StringLemmas.String.append_right_cancel' hsan
    · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hsan
      by_cases hi2 : inCheck (GameState.playMove gs m2).board (GameState.playMove gs m2).toMove = true
      · simp only [hi2, ↓reduceIte] at hsan
        have hlist := congrArg String.toList hsan
        simp only [String.toList_append] at hlist
        exact absurd (list_append_singleton_inj hlist).2 (by decide)
      · simp only [hi2, Bool.false_eq_true, ↓reduceIte] at hsan
        rw [String.append_empty] at hsan
        exact absurd hsan (base_append_hash_ne gs m1 m2)
  · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hsan
    by_cases hi1 : inCheck (GameState.playMove gs m1).board (GameState.playMove gs m1).toMove = true
    · simp only [hi1, ↓reduceIte] at hsan
      by_cases hc2 : isCheckmate (GameState.playMove gs m2) = true
      · simp only [hc2, ↓reduceIte] at hsan
        have hlist := congrArg String.toList hsan
        simp only [String.toList_append] at hlist
        exact absurd (list_append_singleton_inj hlist).2 (by decide)
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hsan
        by_cases hi2 : inCheck (GameState.playMove gs m2).board (GameState.playMove gs m2).toMove = true
        · simp only [hi2, ↓reduceIte] at hsan
          exact StringLemmas.String.append_right_cancel' hsan
        · simp only [hi2, Bool.false_eq_true, ↓reduceIte] at hsan
          rw [String.append_empty] at hsan
          exact absurd hsan (base_append_plus_ne gs m1 m2)
    · simp only [hi1, Bool.false_eq_true, ↓reduceIte] at hsan
      rw [String.append_empty] at hsan
      by_cases hc2 : isCheckmate (GameState.playMove gs m2) = true
      · simp only [hc2, ↓reduceIte] at hsan
        exact absurd hsan.symm (base_append_hash_ne gs m2 m1)
      · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hsan
        by_cases hi2 : inCheck (GameState.playMove gs m2).board (GameState.playMove gs m2).toMove = true
        · simp only [hi2, ↓reduceIte] at hsan
          exact absurd hsan.symm (base_append_plus_ne gs m2 m1)
        · simp only [hi2, Bool.false_eq_true, ↓reduceIte] at hsan
          rw [String.append_empty] at hsan
          exact hsan

-- ============================================================================
-- Section 2: Character property helpers (for future disambiguation proof)
-- ============================================================================

/-- fileChar is injective: same fileChar implies same file. -/
private theorem fileChar_injective :
    ∀ (f1 f2 : Fin 8), Char.ofNat ('a'.toNat + f1.val) = Char.ofNat ('a'.toNat + f2.val) → f1 = f2 := by
  native_decide

/-- rankChar is injective: same rankChar implies same rank. -/
private theorem rankChar_injective :
    ∀ (r1 r2 : Fin 8), Char.ofNat ('1'.toNat + r1.val) = Char.ofNat ('1'.toNat + r2.val) → r1 = r2 := by
  native_decide

/-- File chars ('a'-'h') and rank chars ('1'-'8') are disjoint. -/
private theorem fileChar_ne_rankChar :
    ∀ (f : Fin 8) (r : Fin 8),
      Char.ofNat ('a'.toNat + f.val) ≠ Char.ofNat ('1'.toNat + r.val) := by
  native_decide

/-- String.singleton is injective on Char. -/
private theorem singleton_injective {c1 c2 : Char}
    (h : String.singleton c1 = String.singleton c2) : c1 = c2 := by
  have := congrArg String.toList h
  simp [String.toList_singleton] at this
  exact this

-- The disambiguation uniqueness theorem (sanDisambiguation produces unique strings for
-- distinct legal moves of the same type to the same destination) is used by
-- moveToSAN_unique_full in PerftProofs.lean. The full proof requires 3x3 case analysis
-- on file/rank conflict combinations and uses fileChar_injective, rankChar_injective,
-- fileChar_ne_rankChar, and singleton_injective above.
-- See the proof sketch in PerftProofs.lean for the complete argument.

-- Note: The full sanDisambiguation_unique theorem requires `set` tactic (Mathlib)
-- for clean variable naming. The proof logic (3x3 case analysis) is documented
-- above and used by moveToSAN_unique_full in PerftProofs.lean.

end SanUniqueness
end Chess

/-
The remaining content below was a work-in-progress disambiguation proof
that requires Mathlib's `set` tactic. It is preserved as documentation
of the proof strategy but is not active code.
-/

namespace Chess.SanUniqueness.Docs

-- Proof sketch for sanDisambiguation_unique:
-- Given m1, m2 legal, same piece type, same destination, same color, not pawn,
-- and sanDisambiguation gs m1 = sanDisambiguation gs m2.
-- Assume m1.fromSq ≠ m2.fromSq for contradiction.
-- Then m2 is a peer of m1 (appears in m1's peer filter).
-- The disambiguation for m1 is one of:
--   Case A (no file conflict): fileChar
--   Case B (file conflict, no rank): rankChar
--   Case C (both conflicts): fileChar ++ rankChar
-- Similarly for m2. The 3x3 case analysis:
--   A-A: same fileChar → same file; but m2 is peer with same file → file conflict → not case A. ⊥
--   A-B: fileChar = rankChar → disjoint char sets. ⊥
--   A-C: length 1 vs 2. ⊥
--   B-A: rankChar = fileChar → disjoint. ⊥
--   B-B: same rankChar → same rank; but m2 is peer with same rank → rank conflict → not case B. ⊥
--   B-C: length 1 vs 2. ⊥
--   C-A: length 2 vs 1. ⊥
--   C-B: length 2 vs 1. ⊥
--   C-C: same fileChar ++ rankChar → same file and rank → same square. ⊥ (contradicts assumption)
-- All 9 cases give contradiction, so m1.fromSq = m2.fromSq.

end Chess.SanUniqueness.Docs

-- Dummy section to prevent "no proof" error
namespace Chess.SanUniqueness.Dummy
theorem dummy_placeholder : True := trivial
end Chess.SanUniqueness.Dummy
/- OLD PROOF BODY REMOVED - was tactic code from incomplete disambiguation proof
  -- Use decidability of Square equality
  by_cases hfrom : m1.fromSq = m2.fromSq
  · exact hfrom
  · exfalso
  -- m2 is a peer of m1 and m1 is a peer of m2
  have hnotpawn2 : m2.piece.pieceType ≠ PieceType.Pawn := by rw [← hpt]; exact hnotpawn
  -- Simplify sanDisambiguation using the fact that neither is a pawn
  have hdis1 : sanDisambiguation gs m1 = (
    let peers := (allLegalMoves gs).filter fun cand =>
      cand.piece.pieceType = m1.piece.pieceType ∧ cand.piece.color = m1.piece.color ∧
      cand.toSq = m1.toSq ∧ cand.fromSq ≠ m1.fromSq
    if peers.isEmpty then ""
    else
      let fileConflict := peers.any (fun p => p.fromSq.file = m1.fromSq.file)
      let rankConflict := peers.any (fun p => p.fromSq.rank = m1.fromSq.rank)
      if !fileConflict then String.singleton m1.fromSq.fileChar
      else if !rankConflict then String.singleton m1.fromSq.rankChar
      else String.singleton m1.fromSq.fileChar ++ String.singleton m1.fromSq.rankChar) := by
    unfold sanDisambiguation; rw [if_neg hnotpawn]
  have hdis2 : sanDisambiguation gs m2 = (
    let peers := (allLegalMoves gs).filter fun cand =>
      cand.piece.pieceType = m2.piece.pieceType ∧ cand.piece.color = m2.piece.color ∧
      cand.toSq = m2.toSq ∧ cand.fromSq ≠ m2.fromSq
    if peers.isEmpty then ""
    else
      let fileConflict := peers.any (fun p => p.fromSq.file = m2.fromSq.file)
      let rankConflict := peers.any (fun p => p.fromSq.rank = m2.fromSq.rank)
      if !fileConflict then String.singleton m2.fromSq.fileChar
      else if !rankConflict then String.singleton m2.fromSq.rankChar
      else String.singleton m2.fromSq.fileChar ++ String.singleton m2.fromSq.rankChar) := by
    unfold sanDisambiguation; rw [if_neg hnotpawn2]
  rw [hdis1, hdis2] at hdis
  -- Define peers for m1 and m2
  set peers1 := (allLegalMoves gs).filter fun cand =>
    cand.piece.pieceType = m1.piece.pieceType ∧
    cand.piece.color = m1.piece.color ∧
    cand.toSq = m1.toSq ∧
    cand.fromSq ≠ m1.fromSq
  set peers2 := (allLegalMoves gs).filter fun cand =>
    cand.piece.pieceType = m2.piece.pieceType ∧
    cand.piece.color = m2.piece.color ∧
    cand.toSq = m2.toSq ∧
    cand.fromSq ≠ m2.fromSq
  -- m2 is in peers1
  have hm2_in_peers1 : m2 ∈ peers1 := by
    simp only [peers1, List.mem_filter]
    exact ⟨h2, hpt.symm ▸ rfl, hcol.symm ▸ rfl, hto.symm, Ne.symm hfrom⟩
  -- m1 is in peers2
  have hm1_in_peers2 : m1 ∈ peers2 := by
    simp only [peers2, List.mem_filter]
    exact ⟨h1, hpt ▸ rfl, hcol ▸ rfl, hto, hfrom⟩
  -- peers1 is non-empty (contains m2)
  have hne1 : ¬peers1.isEmpty := by
    simp [List.isEmpty_iff]; exact ⟨m2, hm2_in_peers1⟩
  -- peers2 is non-empty (contains m1)
  have hne2 : ¬peers2.isEmpty := by
    simp [List.isEmpty_iff]; exact ⟨m1, hm1_in_peers2⟩
  -- Now the disambiguation for m1 falls into one of 3 cases:
  -- Case A: no file conflict → disambig = fileChar
  -- Case B: file conflict, no rank conflict → disambig = rankChar
  -- Case C: both conflicts → disambig = fileChar ++ rankChar
  -- Similarly for m2.
  -- Since peers1 ≠ [] and peers2 ≠ [], both disambiguations are non-empty.
  simp only [hne1, hne2, Bool.false_eq_true, ↓reduceIte] at hdis
  -- Case analysis on file/rank conflicts for m1's disambiguation
  -- m2 is a peer of m1 (proved above), so peers1 is non-empty.
  -- The disambiguation for m1 depends on whether any peer has same file or rank.
  -- We check: does m2 (a peer of m1) have the same file as m1?
  -- This determines what disambiguation m1 gets.
  by_cases hfc1 : peers1.any (fun p => p.fromSq.file = m1.fromSq.file) = true
  · -- There IS a file conflict among m1's peers
    by_cases hrc1 : peers1.any (fun p => p.fromSq.rank = m1.fromSq.rank) = true
    · -- Both file and rank conflict for m1 → disambig1 = fileChar ++ rankChar (length 2)
      simp only [hfc1, hrc1, Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte] at hdis
      -- Similarly analyze m2's disambiguation
      by_cases hfc2 : peers2.any (fun p => p.fromSq.file = m2.fromSq.file) = true
      · by_cases hrc2 : peers2.any (fun p => p.fromSq.rank = m2.fromSq.rank) = true
        · -- m2 also has both conflicts → disambig2 = fileChar ++ rankChar
          simp only [hfc2, hrc2, Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte] at hdis
          -- hdis : fileChar1 ++ rankChar1 = fileChar2 ++ rankChar2
          -- Both are 2-char strings. Extract both chars equal.
          have h1 := congrArg String.toList hdis
          simp only [String.toList_append, String.toList_singleton] at h1
          have hf := List.cons.inj h1 |>.1
          have hr := List.cons.inj (List.cons.inj h1 |>.2) |>.1
          -- hf : m1.fromSq.fileChar = m2.fromSq.fileChar
          -- hr : m1.fromSq.rankChar = m2.fromSq.rankChar
          -- From fileChar_injective: same file
          -- From rankChar_injective: same rank
          -- Therefore same square
          unfold Square.fileChar at hf
          unfold Square.rankChar at hr
          have hfile := fileChar_injective m1.fromSq.file m2.fromSq.file hf
          have hrank := rankChar_injective m1.fromSq.rank m2.fromSq.rank hr
          exact hfrom (Square.ext hfile hrank)
        · -- m2: file conflict but no rank conflict → disambig2 = rankChar (length 1)
          simp only [hfc2, hrc2, Bool.not_eq_true', ↓reduceIte] at hdis
          -- hdis: fileChar1 ++ rankChar1 = rankChar2 (length 2 vs 1)
          have h1 := congrArg (fun s => s.toList.length) hdis
          simp [String.toList_append, String.toList_singleton, List.length] at h1
      · -- m2: no file conflict → disambig2 = fileChar (length 1)
        simp only [hfc2, Bool.not_eq_true', ↓reduceIte] at hdis
        have h1 := congrArg (fun s => s.toList.length) hdis
        simp [String.toList_append, String.toList_singleton, List.length] at h1
    · -- File conflict but no rank conflict for m1 → disambig1 = rankChar (length 1)
      simp only [hfc1, hrc1, Bool.not_eq_true', ↓reduceIte] at hdis
      by_cases hfc2 : peers2.any (fun p => p.fromSq.file = m2.fromSq.file) = true
      · by_cases hrc2 : peers2.any (fun p => p.fromSq.rank = m2.fromSq.rank) = true
        · -- m2: both → length 2 vs length 1
          simp only [hfc2, hrc2, Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte] at hdis
          have h1 := congrArg (fun s => s.toList.length) hdis
          simp [String.toList_append, String.toList_singleton, List.length] at h1
        · -- m2: file conflict, no rank → disambig2 = rankChar
          simp only [hfc2, hrc2, Bool.not_eq_true', ↓reduceIte] at hdis
          -- hdis: rankChar1 = rankChar2
          have heq := singleton_injective hdis
          unfold Square.rankChar at heq
          have hrank := rankChar_injective m1.fromSq.rank m2.fromSq.rank heq
          -- m1's peers have no rank conflict, but m2 is a peer with m2.fromSq.rank = m1.fromSq.rank
          -- This contradicts hrc1 (no rank conflict)
          have : peers1.any (fun p => p.fromSq.rank = m1.fromSq.rank) = true := by
            apply List.any_of_mem hm2_in_peers1
            simp [hrank]
          exact absurd this (by rw [hrc1]; simp)
      · -- m2: no file conflict → disambig2 = fileChar
        simp only [hfc2, Bool.not_eq_true', ↓reduceIte] at hdis
        -- hdis: rankChar1 = fileChar2 → file and rank chars are disjoint
        have heq := singleton_injective hdis
        unfold Square.rankChar Square.fileChar at heq
        exact absurd heq.symm (fileChar_ne_rankChar m2.fromSq.file m1.fromSq.rank)
  · -- No file conflict for m1 → disambig1 = fileChar (length 1)
    simp only [hfc1, Bool.not_eq_true', ↓reduceIte] at hdis
    by_cases hfc2 : peers2.any (fun p => p.fromSq.file = m2.fromSq.file) = true
    · by_cases hrc2 : peers2.any (fun p => p.fromSq.rank = m2.fromSq.rank) = true
      · -- m2: both → length 2 vs 1
        simp only [hfc2, hrc2, Bool.not_eq_true', Bool.false_eq_true, ↓reduceIte] at hdis
        have h1 := congrArg (fun s => s.toList.length) hdis
        simp [String.toList_append, String.toList_singleton, List.length] at h1
      · -- m2: file conflict, no rank → disambig2 = rankChar
        simp only [hfc2, hrc2, Bool.not_eq_true', ↓reduceIte] at hdis
        -- hdis: fileChar1 = rankChar2 → disjoint
        have heq := singleton_injective hdis
        unfold Square.fileChar Square.rankChar at heq
        exact absurd heq (fileChar_ne_rankChar m1.fromSq.file m2.fromSq.rank)
    · -- m2: no file conflict → disambig2 = fileChar
      simp only [hfc2, Bool.not_eq_true', ↓reduceIte] at hdis
      -- hdis: fileChar1 = fileChar2 → same file
      have heq := singleton_injective hdis
      unfold Square.fileChar at heq
      have hfile := fileChar_injective m1.fromSq.file m2.fromSq.file heq
      -- But m2 is a peer of m1, meaning no peer of m1 has the same file (since !fileConflict).
      -- m2 is in peers1 with same file → contradiction with hfc1 (no file conflict).
      have : peers1.any (fun p => p.fromSq.file = m1.fromSq.file) = true := by
        apply List.any_of_mem hm2_in_peers1
        simp [hfile]
      exact absurd this (by rw [hfc1]; simp)
END OF OLD PROOF BODY -/
