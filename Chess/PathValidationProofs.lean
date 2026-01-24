import Chess.Core
import Chess.Movement
import Chess.Rules
import Chess.Game

namespace Chess

-- ============================================================================
-- Path Validation Lemmas
-- ============================================================================
-- Formal proofs for sliding piece path validation.
-- Note: Some complex proofs use sorry due to API changes in Lean 4.
-- TODO: Complete these proofs for the current Lean 4 version.

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
  have hf_int : (Int.ofNat sq.file.toNat) < 8 := Int.ofNat_lt.mpr hf
  have hr_int : (Int.ofNat sq.rank.toNat) < 8 := Int.ofNat_lt.mpr hr
  have hf_nonneg : (0 : Int) ≤ Int.ofNat sq.file.toNat := Int.natCast_nonneg _
  have hr_nonneg : (0 : Int) ≤ Int.ofNat sq.rank.toNat := Int.natCast_nonneg _
  have hcond : 0 ≤ Int.ofNat sq.file.toNat ∧ Int.ofNat sq.file.toNat < 8 ∧
               0 ≤ Int.ofNat sq.rank.toNat ∧ Int.ofNat sq.rank.toNat < 8 :=
    ⟨hf_nonneg, hf_int, hr_nonneg, hr_int⟩
  rw [if_pos hcond]
  simp only [Int.toNat, Square.mkUnsafe, Square.mk?, File.toNat, Rank.toNat, hf, hr, ↓reduceDIte]

end Movement

namespace Rules

-- ============================================================================
-- Rook Movement Lemmas
-- ============================================================================

/--
For a rook move, the delta is in the standard rook deltas list.
-/
theorem rookDelta_in_deltas (src tgt : Square) (h : Movement.isRookMove src tgt) :
    Movement.rookDelta src tgt ∈ [(1, 0), (-1, 0), (0, 1), (0, -1)] := by
  unfold Movement.isRookMove at h
  obtain ⟨h_ne, h_axis⟩ := h
  unfold Movement.rookDelta Movement.signInt
  cases h_axis with
  | inl hfd =>
    simp only [hfd.1, ↓reduceIte]
    have hrd := hfd.2
    by_cases h_neg_zero : -Movement.rankDiff src tgt = 0
    · exfalso; omega
    · simp only [h_neg_zero, ↓reduceIte]
      by_cases h_neg_pos : -Movement.rankDiff src tgt > 0
      · simp only [h_neg_pos, ↓reduceIte]; decide
      · simp only [h_neg_pos, ↓reduceIte]; decide
  | inr hrd =>
    have hfd := hrd.2
    by_cases hfd_zero : Movement.fileDiff src tgt = 0
    · simp only [hfd_zero, ↓reduceIte]; exfalso; exact hfd hfd_zero
    · simp only [hfd_zero, ↓reduceIte]
      by_cases h_neg_zero : -Movement.fileDiff src tgt = 0
      · exfalso; omega
      · simp only [h_neg_zero, ↓reduceIte]
        by_cases h_neg_pos : -Movement.fileDiff src tgt > 0
        · simp only [h_neg_pos, ↓reduceIte]; decide
        · simp only [h_neg_pos, ↓reduceIte]; decide

/--
For a rook move, rookOffset is positive.
-/
theorem rookOffset_pos (src tgt : Square) (h : Movement.isRookMove src tgt) :
    Movement.rookOffset src tgt > 0 := by
  unfold Movement.isRookMove at h
  obtain ⟨h_ne, h_axis⟩ := h
  unfold Movement.rookOffset
  cases h_axis with
  | inl hfd =>
    simp only [hfd.1, Int.natAbs_zero, Nat.zero_add]
    exact Int.natAbs_pos.mpr hfd.2
  | inr hrd =>
    simp only [hrd.1, Int.natAbs_zero, Nat.add_zero]
    exact Int.natAbs_pos.mpr hrd.2

/--
For a rook move, rookOffset ≤ 7.
-/
theorem rookOffset_le_7 (src tgt : Square) (h : Movement.isRookMove src tgt) :
    Movement.rookOffset src tgt ≤ 7 := by
  unfold Movement.isRookMove at h
  obtain ⟨h_ne, h_axis⟩ := h
  unfold Movement.rookOffset Movement.fileDiff Movement.rankDiff
  have hf_src_ge : 0 ≤ src.fileInt := Square.fileInt_nonneg src
  have hr_src_ge : 0 ≤ src.rankInt := Square.rankInt_nonneg src
  have hf_tgt_ge : 0 ≤ tgt.fileInt := Square.fileInt_nonneg tgt
  have hr_tgt_ge : 0 ≤ tgt.rankInt := Square.rankInt_nonneg tgt
  have hf_src_lt : src.fileInt < 8 := Square.fileInt_lt_8 src
  have hr_src_lt : src.rankInt < 8 := Square.rankInt_lt_8 src
  have hf_tgt_lt : tgt.fileInt < 8 := Square.fileInt_lt_8 tgt
  have hr_tgt_lt : tgt.rankInt < 8 := Square.rankInt_lt_8 tgt
  have hf_diff_bound : Int.natAbs (src.fileInt - tgt.fileInt) ≤ 7 := by omega
  have hr_diff_bound : Int.natAbs (src.rankInt - tgt.rankInt) ≤ 7 := by omega
  cases h_axis with
  | inl hfd =>
    have hfd_zero : src.fileInt - tgt.fileInt = 0 := hfd.1
    simp only [hfd_zero, Int.natAbs_zero, Nat.zero_add]
    exact hr_diff_bound
  | inr hrd =>
    have hrd_zero : src.rankInt - tgt.rankInt = 0 := hrd.1
    simp only [hrd_zero, Int.natAbs_zero, Nat.add_zero]
    exact hf_diff_bound

-- ============================================================================
-- Bishop Delta, Offset helpers
-- ============================================================================

/-- absInt equals Int.natAbs cast to Int -/
private theorem absInt_eq_natAbs (x : Int) : Movement.absInt x = ↑(Int.natAbs x) := by
  unfold Movement.absInt
  by_cases h : 0 ≤ x
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

/-- For a diagonal move, fileDiff is nonzero. -/
theorem isDiagonal_fileDiff_ne_zero (src tgt : Square) (h : Movement.isDiagonal src tgt) :
    Movement.fileDiff src tgt ≠ 0 := by
  obtain ⟨h_ne, h_abs_eq⟩ := h
  intro h_fd_zero
  have h_rd_zero : Movement.rankDiff src tgt = 0 := by
    rw [absInt_eq_natAbs, absInt_eq_natAbs] at h_abs_eq
    rw [h_fd_zero] at h_abs_eq
    simp at h_abs_eq
    omega
  have h_eq : src = tgt := Square.ext_fileInt_rankInt
    (by unfold Movement.fileDiff at h_fd_zero; omega)
    (by unfold Movement.rankDiff at h_rd_zero; omega)
  exact h_ne h_eq

/-- For a diagonal move, rankDiff is nonzero. -/
theorem isDiagonal_rankDiff_ne_zero (src tgt : Square) (h : Movement.isDiagonal src tgt) :
    Movement.rankDiff src tgt ≠ 0 := by
  obtain ⟨h_ne, h_abs_eq⟩ := h
  intro h_rd_zero
  have h_fd_zero : Movement.fileDiff src tgt = 0 := by
    rw [absInt_eq_natAbs, absInt_eq_natAbs] at h_abs_eq
    rw [h_rd_zero] at h_abs_eq
    simp at h_abs_eq
    omega
  have h_eq : src = tgt := Square.ext_fileInt_rankInt
    (by unfold Movement.fileDiff at h_fd_zero; omega)
    (by unfold Movement.rankDiff at h_rd_zero; omega)
  exact h_ne h_eq

/-- For a diagonal move, |fileDiff| = |rankDiff| as Nats. -/
theorem isDiagonal_natAbs_eq (src tgt : Square) (h : Movement.isDiagonal src tgt) :
    Int.natAbs (Movement.fileDiff src tgt) = Int.natAbs (Movement.rankDiff src tgt) := by
  have h_abs_eq := h.2
  rw [absInt_eq_natAbs, absInt_eq_natAbs] at h_abs_eq
  exact Int.ofNat.inj h_abs_eq

/-- For a diagonal move, bishopDelta is one of the four diagonal unit vectors. -/
theorem bishopDelta_in_deltas (src tgt : Square) (h : Movement.isDiagonal src tgt) :
    Movement.bishopDelta src tgt ∈ [(1, 1), (-1, -1), (1, -1), (-1, 1)] := by
  have hfd_ne := isDiagonal_fileDiff_ne_zero src tgt h
  have hrd_ne := isDiagonal_rankDiff_ne_zero src tgt h
  unfold Movement.bishopDelta Movement.signInt
  by_cases h_fd_neg_zero : -Movement.fileDiff src tgt = 0
  · exfalso; omega
  · simp only [h_fd_neg_zero, ↓reduceIte]
    by_cases h_rd_neg_zero : -Movement.rankDiff src tgt = 0
    · exfalso; omega
    · simp only [h_rd_neg_zero, ↓reduceIte]
      by_cases h_fd_neg_pos : -Movement.fileDiff src tgt > 0
      · simp only [h_fd_neg_pos, ↓reduceIte]
        by_cases h_rd_neg_pos : -Movement.rankDiff src tgt > 0
        · simp only [h_rd_neg_pos, ↓reduceIte]; decide
        · simp only [h_rd_neg_pos, ↓reduceIte]; decide
      · simp only [h_fd_neg_pos, ↓reduceIte]
        by_cases h_rd_neg_pos : -Movement.rankDiff src tgt > 0
        · simp only [h_rd_neg_pos, ↓reduceIte]; decide
        · simp only [h_rd_neg_pos, ↓reduceIte]; decide

/-- For a diagonal move, bishopOffset is positive. -/
theorem bishopOffset_pos (src tgt : Square) (h : Movement.isDiagonal src tgt) :
    Movement.bishopOffset src tgt > 0 := by
  unfold Movement.bishopOffset
  exact Int.natAbs_pos.mpr (isDiagonal_fileDiff_ne_zero src tgt h)

/-- For a diagonal move, bishopOffset ≤ 7. -/
theorem bishopOffset_le_7 (src tgt : Square) (h : Movement.isDiagonal src tgt) :
    Movement.bishopOffset src tgt ≤ 7 := by
  unfold Movement.bishopOffset Movement.fileDiff
  have hf_src_ge : 0 ≤ src.fileInt := Square.fileInt_nonneg src
  have hf_tgt_ge : 0 ≤ tgt.fileInt := Square.fileInt_nonneg tgt
  have hf_src_lt : src.fileInt < 8 := Square.fileInt_lt_8 src
  have hf_tgt_lt : tgt.fileInt < 8 := Square.fileInt_lt_8 tgt
  have hf_diff_bound : Int.natAbs (src.fileInt - tgt.fileInt) ≤ 7 := by omega
  exact hf_diff_bound

-- ============================================================================
-- Intermediate Square Validity & Membership
-- ============================================================================

/--
For a rook move, each intermediate offset k produces a valid square.
-/
theorem rookRay_intermediate_valid (src tgt : Square) (h : Movement.isRookMove src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < Movement.rookOffset src tgt) :
    let (df, dr) := Movement.rookDelta src tgt
    ∃ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq := by
  -- Coordinate bounds
  have hf_src_ge : 0 ≤ src.fileInt := Square.fileInt_nonneg src
  have hr_src_ge : 0 ≤ src.rankInt := Square.rankInt_nonneg src
  have hf_tgt_ge : 0 ≤ tgt.fileInt := Square.fileInt_nonneg tgt
  have hr_tgt_ge : 0 ≤ tgt.rankInt := Square.rankInt_nonneg tgt
  have hf_src_lt : src.fileInt < 8 := Square.fileInt_lt_8 src
  have hr_src_lt : src.rankInt < 8 := Square.rankInt_lt_8 src
  have hf_tgt_lt : tgt.fileInt < 8 := Square.fileInt_lt_8 tgt
  have hr_tgt_lt : tgt.rankInt < 8 := Square.rankInt_lt_8 tgt
  have hk_le : k ≤ Movement.rookOffset src tgt := Nat.le_of_lt hk_lt
  -- Unfold definitions and case split
  unfold Movement.isRookMove at h
  obtain ⟨h_ne, h_axis⟩ := h
  simp only
  cases h_axis with
  | inl hfd =>
    -- Vertical move: fileDiff = 0, rankDiff ≠ 0
    have hfd_eq : Movement.fileDiff src tgt = 0 := hfd.1
    have hrd_ne : Movement.rankDiff src tgt ≠ 0 := hfd.2
    unfold Movement.rookDelta
    simp only [hfd_eq, ↓reduceIte]
    -- rookOffset = |rd|
    have hOffset : Movement.rookOffset src tgt = (Movement.rankDiff src tgt).natAbs := by
      simp only [Movement.rookOffset, hfd_eq, Int.natAbs_zero, Nat.zero_add]
    -- Show bounds on the rank coordinate
    unfold Movement.squareFromInts
    -- File coordinate: src.fileInt + 0 * k = src.fileInt, which is in [0,8)
    have hf_bounds : 0 ≤ src.fileInt + 0 * (k : Int) ∧ src.fileInt + 0 * (k : Int) < 8 := by
      simp only [Int.zero_mul, Int.add_zero]
      exact ⟨hf_src_ge, hf_src_lt⟩
    -- Rank coordinate bounds depend on direction
    have hr_bounds : 0 ≤ src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (k : Int) ∧
                     src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (k : Int) < 8 := by
      unfold Movement.signInt
      by_cases h0 : -Movement.rankDiff src tgt = 0
      · exfalso; omega
      · simp only [h0, ↓reduceIte]
        by_cases hpos : -Movement.rankDiff src tgt > 0
        · -- Moving towards higher rank (signInt = 1)
          simp only [hpos, ↓reduceIte, Int.one_mul]
          unfold Movement.rankDiff at h0 hpos hrd_ne hOffset
          have hk_int : (k : Int) ≤ (Movement.rookOffset src tgt : Int) := Int.ofNat_le.mpr hk_le
          rw [hOffset] at hk_int
          have h_rd_neg : src.rankInt - tgt.rankInt < 0 := by omega
          have h_natAbs : (src.rankInt - tgt.rankInt).natAbs = (tgt.rankInt - src.rankInt).toNat := by
            have h_swap : (src.rankInt - tgt.rankInt).natAbs = (tgt.rankInt - src.rankInt).natAbs := by
              rw [← Int.natAbs_neg (src.rankInt - tgt.rankInt)]; congr 1; omega
            rw [h_swap]
            exact Int.toNat_of_nonneg (by omega : tgt.rankInt - src.rankInt ≥ 0) ▸ rfl
          rw [h_natAbs] at hk_int
          have h_toNat : ((tgt.rankInt - src.rankInt).toNat : Int) = tgt.rankInt - src.rankInt :=
            Int.toNat_of_nonneg (by omega : tgt.rankInt - src.rankInt ≥ 0)
          rw [h_toNat] at hk_int
          constructor <;> omega
        · -- Moving towards lower rank (signInt = -1)
          simp only [hpos, ↓reduceIte]
          unfold Movement.rankDiff at h0 hpos hrd_ne hOffset
          have hk_int : (k : Int) ≤ (Movement.rookOffset src tgt : Int) := Int.ofNat_le.mpr hk_le
          rw [hOffset] at hk_int
          have h_rd_pos : src.rankInt - tgt.rankInt > 0 := by omega
          have h_natAbs : (src.rankInt - tgt.rankInt).natAbs = (src.rankInt - tgt.rankInt).toNat := by
            exact Int.toNat_of_nonneg (by omega : src.rankInt - tgt.rankInt ≥ 0) ▸ rfl
          rw [h_natAbs] at hk_int
          have h_toNat : ((src.rankInt - tgt.rankInt).toNat : Int) = src.rankInt - tgt.rankInt :=
            Int.toNat_of_nonneg (by omega : src.rankInt - tgt.rankInt ≥ 0)
          rw [h_toNat] at hk_int
          constructor <;> omega
    rw [if_pos ⟨hf_bounds.1, hf_bounds.2, hr_bounds.1, hr_bounds.2⟩]
    exact ⟨_, rfl⟩
  | inr hrd =>
    -- Horizontal move: rankDiff = 0, fileDiff ≠ 0
    have hrd_eq : Movement.rankDiff src tgt = 0 := hrd.1
    have hfd_ne : Movement.fileDiff src tgt ≠ 0 := hrd.2
    unfold Movement.rookDelta
    by_cases hfd_zero : Movement.fileDiff src tgt = 0
    · exfalso; exact hfd_ne hfd_zero
    · simp only [hfd_zero, ↓reduceIte]
      -- rookOffset = |fd|
      have hOffset : Movement.rookOffset src tgt = (Movement.fileDiff src tgt).natAbs := by
        simp only [Movement.rookOffset, hrd_eq, Int.natAbs_zero, Nat.add_zero]
      unfold Movement.squareFromInts
      -- Rank coordinate: src.rankInt + 0 * k = src.rankInt
      have hr_bounds : 0 ≤ src.rankInt + 0 * (k : Int) ∧ src.rankInt + 0 * (k : Int) < 8 := by
        simp only [Int.zero_mul, Int.add_zero]
        exact ⟨hr_src_ge, hr_src_lt⟩
      -- File coordinate bounds depend on direction
      have hf_bounds : 0 ≤ src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (k : Int) ∧
                       src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (k : Int) < 8 := by
        unfold Movement.signInt
        by_cases h0 : -Movement.fileDiff src tgt = 0
        · exfalso; omega
        · simp only [h0, ↓reduceIte]
          by_cases hpos : -Movement.fileDiff src tgt > 0
          · -- Moving towards higher file (signInt = 1)
            simp only [hpos, ↓reduceIte, Int.one_mul]
            unfold Movement.fileDiff at h0 hpos hfd_ne hOffset
            have hk_int : (k : Int) ≤ (Movement.rookOffset src tgt : Int) := Int.ofNat_le.mpr hk_le
            rw [hOffset] at hk_int
            have h_fd_neg : src.fileInt - tgt.fileInt < 0 := by omega
            have h_natAbs : (src.fileInt - tgt.fileInt).natAbs = (tgt.fileInt - src.fileInt).toNat := by
              have h_swap : (src.fileInt - tgt.fileInt).natAbs = (tgt.fileInt - src.fileInt).natAbs := by
                rw [← Int.natAbs_neg (src.fileInt - tgt.fileInt)]; congr 1; omega
              rw [h_swap]
              exact Int.toNat_of_nonneg (by omega : tgt.fileInt - src.fileInt ≥ 0) ▸ rfl
            rw [h_natAbs] at hk_int
            have h_toNat : ((tgt.fileInt - src.fileInt).toNat : Int) = tgt.fileInt - src.fileInt :=
              Int.toNat_of_nonneg (by omega : tgt.fileInt - src.fileInt ≥ 0)
            rw [h_toNat] at hk_int
            constructor <;> omega
          · -- Moving towards lower file (signInt = -1)
            simp only [hpos, ↓reduceIte]
            unfold Movement.fileDiff at h0 hpos hfd_ne hOffset
            have hk_int : (k : Int) ≤ (Movement.rookOffset src tgt : Int) := Int.ofNat_le.mpr hk_le
            rw [hOffset] at hk_int
            have h_fd_pos : src.fileInt - tgt.fileInt > 0 := by omega
            have h_natAbs : (src.fileInt - tgt.fileInt).natAbs = (src.fileInt - tgt.fileInt).toNat := by
              exact Int.toNat_of_nonneg (by omega : src.fileInt - tgt.fileInt ≥ 0) ▸ rfl
            rw [h_natAbs] at hk_int
            have h_toNat : ((src.fileInt - tgt.fileInt).toNat : Int) = src.fileInt - tgt.fileInt :=
              Int.toNat_of_nonneg (by omega : src.fileInt - tgt.fileInt ≥ 0)
            rw [h_toNat] at hk_int
            constructor <;> omega
      rw [if_pos ⟨hf_bounds.1, hf_bounds.2, hr_bounds.1, hr_bounds.2⟩]
      exact ⟨_, rfl⟩

/--
Intermediate squares are in squaresBetween for rook moves.
-/
-- Helper: For a rook move, isDiagonal is false (as a Prop negation)
theorem rook_not_diagonal_prop {src tgt : Square} (h : Movement.isRookMove src tgt) :
    ¬Movement.isDiagonal src tgt := by
  unfold Movement.isDiagonal
  intro ⟨_, hAbs⟩
  obtain ⟨_, hAxis⟩ := h
  cases hAxis with
  | inl hfd =>
    -- fileDiff = 0, so absInt fileDiff = 0 ≠ absInt rankDiff (since rankDiff ≠ 0)
    have hfd0 : Movement.fileDiff src tgt = 0 := hfd.1
    have hrd_ne : Movement.rankDiff src tgt ≠ 0 := hfd.2
    unfold Movement.absInt at hAbs
    rw [hfd0] at hAbs
    split at hAbs <;> split at hAbs <;> omega
  | inr hrd =>
    -- rankDiff = 0, so absInt rankDiff = 0 ≠ absInt fileDiff (since fileDiff ≠ 0)
    have hrd0 : Movement.rankDiff src tgt = 0 := hrd.1
    have hfd_ne : Movement.fileDiff src tgt ≠ 0 := hrd.2
    unfold Movement.absInt at hAbs
    rw [hrd0] at hAbs
    split at hAbs <;> split at hAbs <;> omega

-- Helper: signInt 0 = 0
theorem signInt_zero : Movement.signInt 0 = 0 := by
  unfold Movement.signInt; decide

theorem rookRay_intermediate_in_squaresBetween (src tgt : Square) (h : Movement.isRookMove src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < Movement.rookOffset src tgt) :
    let (df, dr) := Movement.rookDelta src tgt
    ∀ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq →
          sq ∈ Movement.squaresBetween src tgt := by
  -- Case split on fileDiff = 0 to resolve the Decidable.rec in rookDelta
  by_cases hfd_zero : Movement.fileDiff src tgt = 0
  · -- Case: fileDiff = 0 (vertical rook move)
    simp only [Movement.rookDelta, hfd_zero, ↓reduceIte]
    intro sq hSq
    -- In this case, rookDelta = (0, signInt(-rd))
    simp only [Int.zero_mul, Int.add_zero] at hSq
    -- Unfold squaresBetween
    unfold Movement.squaresBetween
    have hNotDiag := rook_not_diagonal_prop h
    rw [if_neg hNotDiag, if_pos h]
    have hOffset_pos := rookOffset_pos src tgt h
    have h_steps_gt_1 : ¬((Movement.fileDiff src tgt).natAbs + (Movement.rankDiff src tgt).natAbs ≤ 1) := by
      unfold Movement.rookOffset at hk_lt hOffset_pos; omega
    rw [if_neg h_steps_gt_1]
    rw [List.mem_filterMap]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [List.mem_range]; unfold Movement.rookOffset at hk_lt; omega
    · simp only
      have h_step_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
      have h_stepFile : Movement.signInt (-Movement.fileDiff src tgt) = 0 := by
        rw [hfd_zero]; simp only [Int.neg_zero]; exact signInt_zero
      simp only [h_stepFile, Int.zero_mul, Int.add_zero, h_step_eq]
      exact hSq
  · -- Case: fileDiff ≠ 0 (horizontal rook move)
    simp only [Movement.rookDelta, hfd_zero, ↓reduceIte]
    intro sq hSq
    -- In this case, rookDelta = (signInt(-fd), 0)
    simp only [Int.zero_mul, Int.add_zero] at hSq
    -- Unfold squaresBetween
    unfold Movement.squaresBetween
    have hNotDiag := rook_not_diagonal_prop h
    rw [if_neg hNotDiag, if_pos h]
    have hOffset_pos := rookOffset_pos src tgt h
    have h_steps_gt_1 : ¬((Movement.fileDiff src tgt).natAbs + (Movement.rankDiff src tgt).natAbs ≤ 1) := by
      unfold Movement.rookOffset at hk_lt hOffset_pos; omega
    rw [if_neg h_steps_gt_1]
    rw [List.mem_filterMap]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [List.mem_range]; unfold Movement.rookOffset at hk_lt; omega
    · simp only
      have h_step_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
      -- For horizontal move, rankDiff = 0
      obtain ⟨_, hAxis⟩ := h
      have hrd_eq : Movement.rankDiff src tgt = 0 := by
        cases hAxis with
        | inl hfd => exfalso; exact hfd_zero hfd.1
        | inr hrd => exact hrd.1
      have h_stepRank : Movement.signInt (-Movement.rankDiff src tgt) = 0 := by
        rw [hrd_eq]; simp only [Int.neg_zero]; exact signInt_zero
      simp only [h_stepRank, Int.zero_mul, Int.add_zero, h_step_eq]
      exact hSq

/--
Bishop version of intermediate validity - for diagonal moves.
-/
-- This proof follows the same pattern as rookRay_intermediate_valid but with 4 cases
-- (diagonal directions) instead of 2 (orthogonal directions). The key is showing that
-- for k < bishopOffset, the coordinates src.fileInt + df*k and src.rankInt + dr*k
-- remain in [0, 7]. This requires case analysis on the direction (df, dr) ∈ {(1,1), (1,-1), (-1,1), (-1,-1)}.
-- The proof structure mirrors the rook case but handles both coordinates changing.
-- Verified by perft tests at runtime.
theorem bishopRay_intermediate_valid (src tgt : Square) (h : Movement.isDiagonal src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < Movement.bishopOffset src tgt) :
    let (df, dr) := Movement.bishopDelta src tgt
    ∃ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq := by
  -- Coordinate bounds
  have hf_src_ge : 0 ≤ src.fileInt := Square.fileInt_nonneg src
  have hr_src_ge : 0 ≤ src.rankInt := Square.rankInt_nonneg src
  have hf_tgt_ge : 0 ≤ tgt.fileInt := Square.fileInt_nonneg tgt
  have hr_tgt_ge : 0 ≤ tgt.rankInt := Square.rankInt_nonneg tgt
  have hf_src_lt : src.fileInt < 8 := Square.fileInt_lt_8 src
  have hr_src_lt : src.rankInt < 8 := Square.rankInt_lt_8 src
  have hf_tgt_lt : tgt.fileInt < 8 := Square.fileInt_lt_8 tgt
  have hr_tgt_lt : tgt.rankInt < 8 := Square.rankInt_lt_8 tgt
  have hk_le : k ≤ Movement.bishopOffset src tgt := Nat.le_of_lt hk_lt
  -- For diagonal, |fileDiff| = |rankDiff|
  obtain ⟨h_ne, h_abs_eq⟩ := h
  -- bishopOffset = |fileDiff|
  have hOffset : Movement.bishopOffset src tgt = (Movement.fileDiff src tgt).natAbs := rfl
  -- So k ≤ |fileDiff|
  have hk_le_fd : k ≤ (Movement.fileDiff src tgt).natAbs := by rw [← hOffset]; exact hk_le
  -- And k ≤ |rankDiff| (since |fileDiff| = |rankDiff|)
  have hk_le_rd : k ≤ (Movement.rankDiff src tgt).natAbs := by
    unfold Movement.absInt at h_abs_eq
    have habs_eq_nat : (Movement.fileDiff src tgt).natAbs = (Movement.rankDiff src tgt).natAbs := by
      split at h_abs_eq <;> split at h_abs_eq <;> omega
    rw [habs_eq_nat] at hk_le_fd
    exact hk_le_fd
  -- fileDiff ≠ 0 because diagonal and k > 0 implies bishopOffset > 0 implies |fd| > 0
  have hfd_ne : Movement.fileDiff src tgt ≠ 0 := by
    intro heq
    rw [heq] at hk_le_fd
    simp at hk_le_fd
    omega
  -- rankDiff ≠ 0 because diagonal (|fd| = |rd| and fd ≠ 0)
  have hrd_ne : Movement.rankDiff src tgt ≠ 0 := by
    intro heq
    rw [heq] at hk_le_rd
    simp at hk_le_rd
    omega
  -- Unfold bishopDelta
  simp only [Movement.bishopDelta]
  -- Need to show coordinates are in bounds
  unfold Movement.squareFromInts
  -- Handle both coordinates using same pattern as rook proof
  have hf_bounds : 0 ≤ src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (k : Int) ∧
                   src.fileInt + Movement.signInt (-Movement.fileDiff src tgt) * (k : Int) < 8 := by
    unfold Movement.signInt
    by_cases h0 : -Movement.fileDiff src tgt = 0
    · exfalso; omega
    · simp only [h0, ↓reduceIte]
      by_cases hpos : -Movement.fileDiff src tgt > 0
      · -- Moving towards higher file (signInt = 1)
        simp only [hpos, ↓reduceIte, Int.one_mul]
        unfold Movement.fileDiff at h0 hpos hfd_ne hOffset hk_le_fd
        have hk_int : (k : Int) ≤ (Movement.bishopOffset src tgt : Int) := Int.ofNat_le.mpr hk_le
        rw [hOffset] at hk_int
        have h_fd_neg : src.fileInt - tgt.fileInt < 0 := by omega
        have h_natAbs : (src.fileInt - tgt.fileInt).natAbs = (tgt.fileInt - src.fileInt).toNat := by
          have h_swap : (src.fileInt - tgt.fileInt).natAbs = (tgt.fileInt - src.fileInt).natAbs := by
            rw [← Int.natAbs_neg (src.fileInt - tgt.fileInt)]; congr 1; omega
          rw [h_swap]
          exact Int.toNat_of_nonneg (by omega : tgt.fileInt - src.fileInt ≥ 0) ▸ rfl
        rw [h_natAbs] at hk_int
        have h_toNat : ((tgt.fileInt - src.fileInt).toNat : Int) = tgt.fileInt - src.fileInt :=
          Int.toNat_of_nonneg (by omega : tgt.fileInt - src.fileInt ≥ 0)
        rw [h_toNat] at hk_int
        constructor <;> omega
      · -- Moving towards lower file (signInt = -1)
        simp only [hpos, ↓reduceIte]
        unfold Movement.fileDiff at h0 hpos hfd_ne hOffset hk_le_fd
        have hk_int : (k : Int) ≤ (Movement.bishopOffset src tgt : Int) := Int.ofNat_le.mpr hk_le
        rw [hOffset] at hk_int
        have h_fd_pos : src.fileInt - tgt.fileInt > 0 := by omega
        have h_natAbs : (src.fileInt - tgt.fileInt).natAbs = (src.fileInt - tgt.fileInt).toNat := by
          exact Int.toNat_of_nonneg (by omega : src.fileInt - tgt.fileInt ≥ 0) ▸ rfl
        rw [h_natAbs] at hk_int
        have h_toNat : ((src.fileInt - tgt.fileInt).toNat : Int) = src.fileInt - tgt.fileInt :=
          Int.toNat_of_nonneg (by omega : src.fileInt - tgt.fileInt ≥ 0)
        rw [h_toNat] at hk_int
        constructor <;> omega
  have hr_bounds : 0 ≤ src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (k : Int) ∧
                   src.rankInt + Movement.signInt (-Movement.rankDiff src tgt) * (k : Int) < 8 := by
    unfold Movement.signInt
    by_cases h0 : -Movement.rankDiff src tgt = 0
    · exfalso; omega
    · simp only [h0, ↓reduceIte]
      by_cases hpos : -Movement.rankDiff src tgt > 0
      · -- Moving towards higher rank (signInt = 1)
        simp only [hpos, ↓reduceIte, Int.one_mul]
        unfold Movement.rankDiff at h0 hpos hrd_ne hk_le_rd
        have hk_int : (k : Int) ≤ (k : Int) := Int.le_refl _
        have h_rd_neg : src.rankInt - tgt.rankInt < 0 := by omega
        have h_natAbs : (src.rankInt - tgt.rankInt).natAbs = (tgt.rankInt - src.rankInt).toNat := by
          have h_swap : (src.rankInt - tgt.rankInt).natAbs = (tgt.rankInt - src.rankInt).natAbs := by
            rw [← Int.natAbs_neg (src.rankInt - tgt.rankInt)]; congr 1; omega
          rw [h_swap]
          exact Int.toNat_of_nonneg (by omega : tgt.rankInt - src.rankInt ≥ 0) ▸ rfl
        rw [h_natAbs] at hk_le_rd
        have h_toNat : ((tgt.rankInt - src.rankInt).toNat : Int) = tgt.rankInt - src.rankInt :=
          Int.toNat_of_nonneg (by omega : tgt.rankInt - src.rankInt ≥ 0)
        have hk_int' : (k : Int) ≤ tgt.rankInt - src.rankInt := by
          calc (k : Int) ≤ (tgt.rankInt - src.rankInt).toNat := Int.ofNat_le.mpr hk_le_rd
               _ = tgt.rankInt - src.rankInt := h_toNat
        constructor <;> omega
      · -- Moving towards lower rank (signInt = -1)
        simp only [hpos, ↓reduceIte]
        unfold Movement.rankDiff at h0 hpos hrd_ne hk_le_rd
        have h_rd_pos : src.rankInt - tgt.rankInt > 0 := by omega
        have h_natAbs : (src.rankInt - tgt.rankInt).natAbs = (src.rankInt - tgt.rankInt).toNat := by
          exact Int.toNat_of_nonneg (by omega : src.rankInt - tgt.rankInt ≥ 0) ▸ rfl
        rw [h_natAbs] at hk_le_rd
        have h_toNat : ((src.rankInt - tgt.rankInt).toNat : Int) = src.rankInt - tgt.rankInt :=
          Int.toNat_of_nonneg (by omega : src.rankInt - tgt.rankInt ≥ 0)
        have hk_int : (k : Int) ≤ src.rankInt - tgt.rankInt := by
          calc (k : Int) ≤ (src.rankInt - tgt.rankInt).toNat := Int.ofNat_le.mpr hk_le_rd
               _ = src.rankInt - tgt.rankInt := h_toNat
        constructor <;> omega
  rw [if_pos ⟨hf_bounds.1, hf_bounds.2, hr_bounds.1, hr_bounds.2⟩]
  exact ⟨_, rfl⟩

-- Bishop intermediate squares are in squaresBetween for diagonal moves.
-- This proof follows the same structure as rookRay_intermediate_in_squaresBetween.
-- The key insight is that squaresBetween for diagonal moves generates squares at offsets 1..K-1
-- using filterMap with indices in range(K-1), so sq at offset k corresponds to index k-1.
-- Verified by perft tests at runtime.
theorem bishopRay_intermediate_in_squaresBetween (src tgt : Square) (h : Movement.isDiagonal src tgt)
    (k : Nat) (hk_pos : 0 < k) (hk_lt : k < Movement.bishopOffset src tgt) :
    let (df, dr) := Movement.bishopDelta src tgt
    ∀ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq →
          sq ∈ Movement.squaresBetween src tgt := by
  simp only [Movement.bishopDelta]
  intro sq hSq
  -- Unfold squaresBetween for diagonal case
  unfold Movement.squaresBetween
  rw [if_pos h]
  -- bishopOffset = |fileDiff|, need steps > 1 since k ≥ 1 and k < offset
  have hOffset : Movement.bishopOffset src tgt = (Movement.fileDiff src tgt).natAbs := rfl
  have h_steps_gt_1 : ¬((Movement.fileDiff src tgt).natAbs ≤ 1) := by
    rw [← hOffset]
    omega
  rw [if_neg h_steps_gt_1]
  rw [List.mem_filterMap]
  -- sq is at index k-1 in the range
  refine ⟨k - 1, ?_, ?_⟩
  · -- k - 1 < steps - 1
    rw [List.mem_range]
    rw [← hOffset]
    omega
  · -- squareFromInts at step k equals some sq
    simp only
    have h_step_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
    simp only [h_step_eq]
    exact hSq

-- ============================================================================
-- Pawn Move Generation Helpers
-- ============================================================================

/--
If a move is in promotionMoves, it's in the foldr result for a single-element list.
-/
theorem pawn_move_in_foldr_head (m mv : Move) :
    m ∈ promotionMoves mv →
    m ∈ [mv].foldr (fun mv' acc => promotionMoves mv' ++ acc) [] := by
  intro h_in_promo
  simp only [List.foldr, List.append_nil]
  exact h_in_promo

/--
If a move is in the foldr result of a list tail, it's in the foldr
result after prepending a new head element.
-/
theorem pawn_move_in_foldr_tail (m mv : Move) (tail : List Move) :
    m ∈ tail.foldr (fun mv' acc => promotionMoves mv' ++ acc) [] →
    m ∈ (mv :: tail).foldr (fun mv' acc => promotionMoves mv' ++ acc) [] := by
  intro h_in_tail
  simp only [List.foldr, List.mem_append]
  right
  exact h_in_tail

end Rules

end Chess
