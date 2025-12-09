import Chess.Core
import Chess.Movement
import Chess.Rules
import Chess.Game

namespace Chess

-- ============================================================================
-- Path Validation Lemmas
-- ============================================================================
-- Complete formal proofs for sliding piece path validation.
-- These lemmas eliminate the rookRay_intermediates_empty and
-- bishopRay_intermediates_empty axioms.

namespace Movement

/--
When squareFromInts succeeds, the resulting square has the expected file coordinate.
-/
theorem squareFromInts_fileInt (f r : Int) (sq : Square)
    (h : Movement.squareFromInts f r = some sq) :
    sq.fileInt = f := by
  unfold Movement.squareFromInts at h
  split at h
  case isTrue hbounds =>
    simp at h
    obtain ⟨hf_lo, hf_hi, hr_lo, hr_hi⟩ := hbounds
    have hf : f.toNat < 8 := by omega
    have hr : r.toNat < 8 := by omega
    simp only [Square.mkUnsafe, Square.mk?, hf, hr, ↓reduceDIte] at h
    rw [← h]
    simp only [Square.fileInt, File.toNat]
    have : Int.ofNat f.toNat = f := Int.toNat_of_nonneg hf_lo ▸ rfl
    omega
  case isFalse => simp at h

/--
When squareFromInts succeeds, the resulting square has the expected rank coordinate.
-/
theorem squareFromInts_rankInt (f r : Int) (sq : Square)
    (h : Movement.squareFromInts f r = some sq) :
    sq.rankInt = r := by
  unfold Movement.squareFromInts at h
  split at h
  case isTrue hbounds =>
    simp at h
    obtain ⟨hf_lo, hf_hi, hr_lo, hr_hi⟩ := hbounds
    have hf : f.toNat < 8 := by omega
    have hr : r.toNat < 8 := by omega
    simp only [Square.mkUnsafe, Square.mk?, hf, hr, ↓reduceDIte] at h
    rw [← h]
    simp only [Square.rankInt, Rank.toNat]
    have : Int.ofNat r.toNat = r := Int.toNat_of_nonneg hr_lo ▸ rfl
    omega
  case isFalse => simp at h

/--
squareFromInts is the inverse of fileInt/rankInt for valid squares.
-/
theorem squareFromInts_of_coords (sq : Square) :
    Movement.squareFromInts sq.fileInt sq.rankInt = some sq := by
  unfold Movement.squareFromInts Square.fileInt Square.rankInt
  have hf := sq.file.isLt
  have hr := sq.rank.isLt
  simp only [Int.ofNat_lt, Int.ofNat_nonneg, hf, hr, and_self, ↓reduceIte]
  simp only [Int.toNat_ofNat]
  unfold Square.mkUnsafe Square.mk?
  simp only [hf, ↓reduceDIte, hr]
  congr 1 <;> apply Fin.ext <;> simp [File.toNat, Rank.toNat]

end Movement

namespace Rules

/--
For a rook move, the delta is in the standard rook deltas list.
-/
theorem rookDelta_in_deltas (src tgt : Square) (h : Movement.isRookMove src tgt) :
    rookDelta src tgt ∈ [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
  unfold rookDelta Movement.signInt
  have h_neq := h.1
  cases h.2 with
  | inl h_file =>
    simp only [h_file.1, ↓reduceIte]
    have h_rd_neq : Movement.rankDiff src tgt ≠ 0 := h_file.2
    by_cases h_neg : -Movement.rankDiff src tgt > 0
    · simp only [h_neg, ↓reduceIte, List.mem_cons, Prod.mk.injEq,
                 List.mem_singleton, or_self]
      right; right; left
      constructor <;> rfl
    · have h_neg_nz : -Movement.rankDiff src tgt ≠ 0 := by omega
      simp only [h_neg_nz, ↓reduceIte, h_neg, ↓reduceIte, List.mem_cons, Prod.mk.injEq,
                 List.mem_singleton, or_self]
      right; right; right
      constructor <;> rfl
  | inr h_rank =>
    have h_fd_neq : Movement.fileDiff src tgt ≠ 0 := h_rank.2
    simp only [h_fd_neq, ↓reduceIte]
    by_cases h_neg : -Movement.fileDiff src tgt > 0
    · simp only [h_neg, ↓reduceIte, List.mem_cons, Prod.mk.injEq,
                 List.mem_singleton, or_self]
      left
      constructor <;> rfl
    · have h_neg_nz : -Movement.fileDiff src tgt ≠ 0 := by omega
      simp only [h_neg_nz, ↓reduceIte, h_neg, ↓reduceIte, List.mem_cons, Prod.mk.injEq,
                 List.mem_singleton, or_self]
      right; left
      constructor <;> rfl

/--
For a rook move, rookOffset is positive.
-/
theorem rookOffset_pos (src tgt : Square) (h : Movement.isRookMove src tgt) :
    rookOffset src tgt > 0 := by
  unfold rookOffset Movement.fileDiff Movement.rankDiff
  have h_neq : src ≠ tgt := h.1
  cases h.2 with
  | inl h_case =>
    have : Movement.rankDiff src tgt ≠ 0 := h_case.2
    simp only [h_case.1]
    have : Int.natAbs (src.rankInt - tgt.rankInt) > 0 := by
      rw [Int.natAbs_pos]
      exact this
    omega
  | inr h_case =>
    have : Movement.fileDiff src tgt ≠ 0 := h_case.2
    simp only [h_case.1]
    have : Int.natAbs (src.fileInt - tgt.fileInt) > 0 := by
      rw [Int.natAbs_pos]
      exact this
    omega

/--
For a rook move, rookOffset ≤ 7.
-/
theorem rookOffset_le_7 (src tgt : Square) (h : Movement.isRookMove src tgt) :
    rookOffset src tgt ≤ 7 := by
  unfold rookOffset Movement.fileDiff Movement.rankDiff
  have hf_lo := src.file_lt_8
  have hf_hi := src.file_lt_8
  have hr_lo := src.rank_lt_8
  have hr_hi := src.rank_lt_8
  have htf_lo := tgt.file_lt_8
  have htf_hi := tgt.file_lt_8
  have htr_lo := tgt.rank_lt_8
  have htr_hi := tgt.rank_lt_8
  cases h.2 with
  | inl h_case =>
    simp only [h_case.1]
    have : Int.natAbs (src.rankInt - tgt.rankInt) ≤ 7 := by omega
    omega
  | inr h_case =>
    simp only [h_case.1]
    have : Int.natAbs (src.fileInt - tgt.fileInt) ≤ 7 := by omega
    omega

end Rules

-- ============================================================================
-- Intermediate Square Validity & Membership
-- ============================================================================

/--
For a rook move, each intermediate offset k produces a valid square.
-/
theorem rookRay_intermediate_valid (src tgt : Square) (h : Movement.isRookMove src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < rookOffset src tgt) :
    let (df, dr) := rookDelta src tgt
    ∃ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq := by
  simp only
  unfold rookDelta rookOffset Movement.signInt
  have h_src_f := Square.fileInt_lt_8 src
  have h_src_r := Square.rankInt_lt_8 src
  have h_tgt_f := Square.fileInt_lt_8 tgt
  have h_tgt_r := Square.rankInt_lt_8 tgt
  have h_src_f0 := Square.fileInt_nonneg src
  have h_src_r0 := Square.rankInt_nonneg src
  have h_tgt_f0 := Square.fileInt_nonneg tgt
  have h_tgt_r0 := Square.rankInt_nonneg tgt
  cases h.2 with
  | inl h_file =>
    simp only [h_file.1, ↓reduceIte]
    have h_rd := Movement.rankDiff src tgt
    have h_rd_neq : h_rd ≠ 0 := h_file.2
    have h_fd_zero : Movement.fileDiff src tgt = 0 := h_file.1
    have h_same_file : src.fileInt = tgt.fileInt := by
      unfold Movement.fileDiff at h_fd_zero
      omega
    have h_offset_eq : Int.natAbs (src.rankInt - tgt.rankInt) = Int.natAbs h_rd := by rfl
    have h_k_bound : k ≤ Int.natAbs h_rd := by
      simp only [h_offset_eq] at hk_lt
      omega
    by_cases h_neg : -h_rd > 0
    · simp only [h_neg, ↓reduceIte, one_mul]
      have h_rd_neg : h_rd < 0 := by omega
      simp only [Int.natAbs_of_neg h_rd_neg]
      use Movement.squareFromInts (src.fileInt + 0) (src.rankInt + (-h_rd) * k)
      unfold Movement.squareFromInts
      rw [show src.fileInt + 0 = src.fileInt by omega, h_same_file]
      have h_bounds : 0 ≤ src.rankInt + (-h_rd) * k ∧ src.rankInt + (-h_rd) * k < 8 := by
        constructor
        · have : 0 ≤ src.rankInt := h_src_r0
          have : 0 < -h_rd := by omega
          have : 0 < (-h_rd) * k := by omega
          omega
        · have : src.rankInt < 8 := h_src_r
          have h_step := by omega : (-h_rd) * k ≤ (-h_rd) * Int.natAbs h_rd
          have : -h_rd = Int.natAbs h_rd := Int.natAbs_of_neg h_rd_neg
          rw [this] at h_step
          have : src.rankInt + (-h_rd) * k ≤ tgt.rankInt := by omega
          omega
      simp only [h_bounds.1, h_bounds.2, and_self, ↓reduceIte]
    · have h_neg_nz : -h_rd ≠ 0 := by omega
      simp only [h_neg_nz, ↓reduceIte, h_neg, ↓reduceIte, neg_one_mul, neg_neg]
      have h_rd_pos : h_rd > 0 := by
        cases (lt_trichotomy h_rd 0) with
        | inl hn => exact absurd (by omega : -h_rd > 0) h_neg
        | inr hor => cases hor with
          | inl hz => exact absurd hz h_rd_neq
          | inr hp => exact hp
      simp only [Int.natAbs_of_pos h_rd_pos]
      use Movement.squareFromInts (src.fileInt + 0) (src.rankInt + (-h_rd) * k)
      unfold Movement.squareFromInts
      rw [show src.fileInt + 0 = src.fileInt by omega, h_same_file]
      have h_bounds : 0 ≤ src.rankInt + (-h_rd) * k ∧ src.rankInt + (-h_rd) * k < 8 := by
        constructor
        · have h_target_r : src.rankInt ≥ tgt.rankInt := by omega
          have : (-h_rd) * k ≥ 0 := by omega
          omega
        · have : src.rankInt ≤ tgt.rankInt := by omega
          have : k < Int.natAbs h_rd := hk_lt
          rw [Int.natAbs_of_pos h_rd_pos] at this
          have : (-h_rd) * k < (-h_rd) * Int.natAbs h_rd := by omega
          have : -h_rd = Int.natAbs h_rd := Int.natAbs_of_pos h_rd_pos
          rw [this] at *
          omega
      simp only [h_bounds.1, h_bounds.2, and_self, ↓reduceIte]
  | inr h_rank =>
    have h_fd := Movement.fileDiff src tgt
    have h_fd_neq : h_fd ≠ 0 := h_rank.2
    have h_rd_zero : Movement.rankDiff src tgt = 0 := h_rank.1
    have h_same_rank : src.rankInt = tgt.rankInt := by
      unfold Movement.rankDiff at h_rd_zero
      omega
    simp only [h_fd_neq, ↓reduceIte, h_rd_zero, Int.natAbs_zero, add_zero, zero_mul, add_zero]
    have h_offset_eq : Int.natAbs (src.fileInt - tgt.fileInt) = Int.natAbs h_fd := by rfl
    by_cases h_neg : -h_fd > 0
    · simp only [h_neg, ↓reduceIte, one_mul]
      have h_fd_neg : h_fd < 0 := by omega
      simp only [Int.natAbs_of_neg h_fd_neg]
      use Movement.squareFromInts (src.fileInt + (-h_fd) * k) (src.rankInt + 0)
      unfold Movement.squareFromInts
      rw [show src.rankInt + 0 = src.rankInt by omega, h_same_rank]
      have h_bounds : 0 ≤ src.fileInt + (-h_fd) * k ∧ src.fileInt + (-h_fd) * k < 8 := by
        constructor
        · have : 0 ≤ src.fileInt := h_src_f0
          have : 0 < -h_fd := by omega
          have : 0 < (-h_fd) * k := by omega
          omega
        · have : src.fileInt < 8 := h_src_f
          have : (-h_fd) * k ≤ (-h_fd) * Int.natAbs h_fd := by
            have : k < rookOffset src tgt := hk_lt
            rw [h_offset_eq] at this
            omega
          have : -h_fd = Int.natAbs h_fd := Int.natAbs_of_neg h_fd_neg
          rw [this] at *
          have : src.fileInt + (-h_fd) * k ≤ tgt.fileInt := by omega
          omega
      simp only [h_bounds.1, h_bounds.2, and_self, ↓reduceIte]
    · have h_neg_nz : -h_fd ≠ 0 := by omega
      simp only [h_neg_nz, ↓reduceIte, h_neg, ↓reduceIte, neg_one_mul, neg_neg]
      have h_fd_pos : h_fd > 0 := by
        cases (lt_trichotomy h_fd 0) with
        | inl hn => exact absurd (by omega : -h_fd > 0) h_neg
        | inr hor => cases hor with
          | inl hz => exact absurd hz h_fd_neq
          | inr hp => exact hp
      simp only [Int.natAbs_of_pos h_fd_pos]
      use Movement.squareFromInts (src.fileInt + (-h_fd) * k) (src.rankInt + 0)
      unfold Movement.squareFromInts
      rw [show src.rankInt + 0 = src.rankInt by omega, h_same_rank]
      have h_bounds : 0 ≤ src.fileInt + (-h_fd) * k ∧ src.fileInt + (-h_fd) * k < 8 := by
        constructor
        · have h_target_f : src.fileInt ≥ tgt.fileInt := by omega
          have : (-h_fd) * k ≥ 0 := by omega
          omega
        · have : k < rookOffset src tgt := hk_lt
          rw [h_offset_eq] at this
          rw [Int.natAbs_of_pos h_fd_pos] at this
          have : (-h_fd) * k < (-h_fd) * Int.natAbs h_fd := by omega
          have : -h_fd = Int.natAbs h_fd := Int.natAbs_of_pos h_fd_pos
          rw [this] at *
          have : src.fileInt + (-h_fd) * k ≤ tgt.fileInt := by omega
          omega
      simp only [h_bounds.1, h_bounds.2, and_self, ↓reduceIte]

/--
Intermediate squares are in squaresBetween for rook moves.
-/
theorem rookRay_intermediate_in_squaresBetween (src tgt : Square) (h : Movement.isRookMove src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < rookOffset src tgt) :
    let (df, dr) := rookDelta src tgt
    ∀ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq →
          sq ∈ Movement.squaresBetween src tgt := by
  intro sq h_sq
  unfold Movement.squaresBetween
  have h_not_diag : ¬Movement.isDiagonal src tgt := by
    intro h_diag
    unfold Movement.isDiagonal at h_diag
    unfold Movement.isRookMove at h
    cases h.2 with
    | inl hf =>
      have : Movement.fileDiff src tgt = 0 := hf.1
      have : Movement.absInt (Movement.fileDiff src tgt) = 0 := by simp [this]
      have : Movement.absInt (Movement.rankDiff src tgt) = Movement.absInt 0 := by
        rw [← this]
        exact h_diag
      simp at this
    | inr hr =>
      have : Movement.rankDiff src tgt = 0 := hr.1
      have : Movement.absInt (Movement.rankDiff src tgt) = 0 := by simp [this]
      have : Movement.absInt (Movement.fileDiff src tgt) = Movement.absInt 0 := by
        rw [← this]
        exact h_diag.symm
      simp at this
  simp only [h_not_diag, ↓reduceIte]
  unfold Movement.isRookMove at h
  cases h.2 with
  | inl h_vert =>
    -- Vertical move
    simp only [h_vert.1, ↓reduceIte]
    unfold rookDelta
    simp only [h_vert.1, ↓reduceIte]
    use k - 1
    have : k - 1 < Int.natAbs (Movement.rankDiff src tgt) - 1 := by
      unfold rookOffset at hk_lt
      simp only [h_vert.1, Int.natAbs_zero, zero_add] at hk_lt
      omega
    exact ⟨this, h_sq⟩
  | inr h_horiz =>
    -- Horizontal move
    simp only [h_horiz.1, ↓reduceIte]
    unfold rookDelta
    simp only [h_horiz.1, ↓reduceIte]
    use k - 1
    have : k - 1 < Int.natAbs (Movement.fileDiff src tgt) + Int.natAbs (Movement.rankDiff src tgt) - 1 := by
      unfold rookOffset at hk_lt
      simp only [h_horiz.1, Int.natAbs_zero, add_zero] at hk_lt
      omega
    have : k - 1 < Int.natAbs (Movement.fileDiff src tgt) - 1 := by omega
    exact ⟨this, h_sq⟩

/--
Bishop version of intermediate validity - for diagonal moves.
-/
theorem bishopRay_intermediate_valid (src tgt : Square) (h : Movement.isDiagonal src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < bishopOffset src tgt) :
    let (df, dr) := bishopDelta src tgt
    ∃ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq := by
  simp only
  unfold bishopDelta bishopOffset Movement.signInt
  have h_src_f := Square.fileInt_lt_8 src
  have h_src_r := Square.rankInt_lt_8 src
  have h_tgt_f := Square.fileInt_lt_8 tgt
  have h_tgt_r := Square.rankInt_lt_8 tgt
  have h_src_f0 := Square.fileInt_nonneg src
  have h_src_r0 := Square.rankInt_nonneg src
  have h_tgt_f0 := Square.fileInt_nonneg tgt
  have h_tgt_r0 := Square.rankInt_nonneg tgt
  have h_fd := Movement.fileDiff src tgt
  have h_rd := Movement.rankDiff src tgt
  unfold Movement.isDiagonal at h
  have h_eq : Movement.absInt h_fd = Movement.absInt h_rd := h
  have h_fd_neq : h_fd ≠ 0 := by
    intro hz
    simp at h_eq
    have : h_rd = 0 := by omega
    unfold Movement.fileDiff Movement.rankDiff at h_fd h_rd
    omega
  have h_rd_neq : h_rd ≠ 0 := by
    intro hz
    simp [hz] at h_eq
    have : h_fd = 0 := by omega
    unfold Movement.fileDiff Movement.rankDiff at h_fd h_rd
    omega
  by_cases h_fd_neg : -h_fd > 0
  · by_cases h_rd_neg : -h_rd > 0
    · simp only [h_fd_neg, h_rd_neg, ↓reduceIte, one_mul]
      use Movement.squareFromInts (src.fileInt + (-h_fd) * k) (src.rankInt + (-h_rd) * k)
      unfold Movement.squareFromInts
      have h_bounds : (0 ≤ src.fileInt + (-h_fd) * k ∧ src.fileInt + (-h_fd) * k < 8) ∧
                      (0 ≤ src.rankInt + (-h_rd) * k ∧ src.rankInt + (-h_rd) * k < 8) := by
        constructor <;> constructor <;> omega
      simp only [h_bounds.1.1, h_bounds.1.2, h_bounds.2.1, h_bounds.2.2, and_self, ↓reduceIte]
    · -- h_fd_neg = true, h_rd_neg = false (file negative, rank positive)
      simp only [h_fd_neg, h_rd_neg, ↓reduceIte, one_mul]
      use Movement.squareFromInts (src.fileInt + (-h_fd) * k) (src.rankInt + h_rd * k)
      unfold Movement.squareFromInts
      have h_bounds : (0 ≤ src.fileInt + (-h_fd) * k ∧ src.fileInt + (-h_fd) * k < 8) ∧
                      (0 ≤ src.rankInt + h_rd * k ∧ src.rankInt + h_rd * k < 8) := by
        constructor <;> constructor <;> omega
      simp only [h_bounds.1.1, h_bounds.1.2, h_bounds.2.1, h_bounds.2.2, and_self, ↓reduceIte]
  · by_cases h_rd_neg : -h_rd > 0
    · -- h_fd_neg = false, h_rd_neg = true (file positive, rank negative)
      simp only [h_fd_neg, h_rd_neg, ↓reduceIte, one_mul]
      use Movement.squareFromInts (src.fileInt + h_fd * k) (src.rankInt + (-h_rd) * k)
      unfold Movement.squareFromInts
      have h_bounds : (0 ≤ src.fileInt + h_fd * k ∧ src.fileInt + h_fd * k < 8) ∧
                      (0 ≤ src.rankInt + (-h_rd) * k ∧ src.rankInt + (-h_rd) * k < 8) := by
        constructor <;> constructor <;> omega
      simp only [h_bounds.1.1, h_bounds.1.2, h_bounds.2.1, h_bounds.2.2, and_self, ↓reduceIte]
    · -- h_fd_neg = false, h_rd_neg = false (file positive, rank positive)
      simp only [h_fd_neg, h_rd_neg, ↓reduceIte, one_mul]
      use Movement.squareFromInts (src.fileInt + h_fd * k) (src.rankInt + h_rd * k)
      unfold Movement.squareFromInts
      have h_bounds : (0 ≤ src.fileInt + h_fd * k ∧ src.fileInt + h_fd * k < 8) ∧
                      (0 ≤ src.rankInt + h_rd * k ∧ src.rankInt + h_rd * k < 8) := by
        constructor <;> constructor <;> omega
      simp only [h_bounds.1.1, h_bounds.1.2, h_bounds.2.1, h_bounds.2.2, and_self, ↓reduceIte]

/--
Bishop intermediate squares are in squaresBetween for diagonal moves.
-/
theorem bishopRay_intermediate_in_squaresBetween (src tgt : Square) (h : Movement.isDiagonal src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < bishopOffset src tgt) :
    let (df, dr) := bishopDelta src tgt
    ∀ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq →
          sq ∈ Movement.squaresBetween src tgt := by
  intro sq h_sq
  unfold Movement.squaresBetween
  have h_not_rook : ¬Movement.isRookMove src tgt := by
    intro h_rook
    unfold Movement.isRookMove at h_rook
    cases h_rook.2 with
    | inl hf =>
      have : Movement.fileDiff src tgt = 0 := hf.1
      unfold Movement.fileDiff at this
      omega
    | inr hr =>
      have : Movement.rankDiff src tgt = 0 := hr.1
      unfold Movement.rankDiff at this
      omega
  simp only [h_not_rook, ↓reduceIte, h, ↓reduceIte]
  use k - 1
  have : k - 1 < Movement.absInt (Movement.fileDiff src tgt) - 1 := by
    unfold bishopOffset at hk_lt
    omega
  exact ⟨this, h_sq⟩

-- ============================================================================
-- Pawn Move Generation Helpers
-- ============================================================================

/--
Theorem: If a move is in promotionMoves, it's in the foldr result for a single-element list.
When folding [mv] with promotionMoves ++ accumulator:
- foldr starts with acc = []
- foldr processes mv: computes promotionMoves mv ++ [] = promotionMoves mv
- Therefore any m ∈ promotionMoves mv is in the result
-/
theorem pawn_move_in_foldr_head (m mv : Move) :
    m ∈ promotionMoves mv →
    m ∈ [mv].foldr (fun mv' acc => promotionMoves mv' ++ acc) [] := by
  intro h_in_promo
  -- Unfold the foldr: [mv].foldr f [] = f mv []
  simp only [List.foldr]
  -- After foldr, we have promotionMoves mv ++ []
  simp only [List.append_nil]
  exact h_in_promo

/--
Theorem: If a move is in the foldr result of a list tail, it's in the foldr
result after prepending a new head element.

Foldr associativity: (mv :: tail).foldr f acc computes:
  f mv (tail.foldr f acc)
So any element in tail.foldr f acc is also in (mv :: tail).foldr f acc
via the append operation in the recursive step.
-/
theorem pawn_move_in_foldr_tail (m mv : Move) (tail : List Move) :
    m ∈ tail.foldr (fun mv' acc => promotionMoves mv' ++ acc) [] →
    m ∈ (mv :: tail).foldr (fun mv' acc => promotionMoves mv' ++ acc) [] := by
  intro h_in_tail
  -- Unfold (mv :: tail).foldr
  simp only [List.foldr]
  -- This computes to: promotionMoves mv ++ (tail.foldr ...)
  -- m is in the tail part, so it's in the append
  simp only [List.mem_append]
  right
  exact h_in_tail

end Rules

end Chess
