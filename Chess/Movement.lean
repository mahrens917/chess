import Chess.Core

namespace Chess

namespace Movement

def fileDiff (source target : Square) : Int := source.fileInt - target.fileInt
def rankDiff (source target : Square) : Int := source.rankInt - target.rankInt

def absInt (x : Int) : Int := if 0 ≤ x then x else -x

def isRookMove (source target : Square) : Prop :=
  source ≠ target ∧
    ((fileDiff source target = 0 ∧ rankDiff source target ≠ 0) ∨ (rankDiff source target = 0 ∧ fileDiff source target ≠ 0))

instance instDecidableIsRookMove (source target : Square) : Decidable (isRookMove source target) := by
  unfold isRookMove
  infer_instance

def isDiagonal (source target : Square) : Prop :=
  source ≠ target ∧ absInt (fileDiff source target) = absInt (rankDiff source target)

instance instDecidableIsDiagonal (source target : Square) : Decidable (isDiagonal source target) := by
  unfold isDiagonal
  infer_instance

def isQueenMove (source target : Square) : Prop :=
  isRookMove source target ∨ isDiagonal source target
instance instDecidableIsQueenMove (source target : Square) : Decidable (isQueenMove source target) := by
  unfold isQueenMove
  infer_instance

def isKingStep (source target : Square) : Prop :=
  source ≠ target ∧ absInt (fileDiff source target) ≤ 1 ∧ absInt (rankDiff source target) ≤ 1

def isKnightMove (source target : Square) : Prop :=
  source ≠ target ∧
    ((absInt (fileDiff source target) = 1 ∧ absInt (rankDiff source target) = 2) ∨
     (absInt (fileDiff source target) = 2 ∧ absInt (rankDiff source target) = 1))

def isKingStepBool (source target : Square) : Bool :=
  if source = target then false else
    let fileDelta := absInt (fileDiff source target)
    let rankDelta := absInt (rankDiff source target)
    if fileDelta ≤ 1 then
      if rankDelta ≤ 1 then true else false
    else
      false

def isKnightMoveBool (source target : Square) : Bool :=
  if source = target then false else
    let fileDelta := absInt (fileDiff source target)
    let rankDelta := absInt (rankDiff source target)
    if fileDelta = 1 then
      if rankDelta = 2 then true else false
    else if fileDelta = 2 then
      if rankDelta = 1 then true else false
    else
      false

def pawnDirection (c : Color) : Int :=
  if c = Color.White then 1 else -1

-- Note: rankDiff = source - target, so for forward movement (target ahead of source):
-- White: target.rank > source.rank → rankDiff < 0, pawnDirection = 1 → use negative
-- Black: target.rank < source.rank → rankDiff > 0, pawnDirection = -1 → use negative
def isPawnAdvance (c : Color) (source target : Square) : Prop :=
  source ≠ target ∧ fileDiff source target = 0 ∧
    (rankDiff source target = -pawnDirection c ∨ rankDiff source target = -2 * pawnDirection c)

-- Pawn captures move 1 square diagonally forward (same direction as advances)
def isPawnCapture (c : Color) (source target : Square) : Prop :=
  source ≠ target ∧ absInt (fileDiff source target) = 1 ∧ rankDiff source target = -pawnDirection c
instance instDecidableIsPawnCapture (c : Color) (source target : Square) : Decidable (isPawnCapture c source target) := by
  unfold isPawnCapture
  infer_instance

def kingTargets (source : Square) : List Square :=
  Square.all.filter fun target => isKingStepBool source target

def knightTargets (source : Square) : List Square :=
  Square.all.filter fun target => isKnightMoveBool source target

def signInt (x : Int) : Int :=
  if x = 0 then 0 else if x > 0 then 1 else -1

def squareFromInts (f r : Int) : Option Square :=
  if 0 ≤ f ∧ f < 8 ∧ 0 ≤ r ∧ r < 8 then
    some <| Square.mkUnsafe (Int.toNat f) (Int.toNat r)
  else
    none

def rookDelta (src tgt : Square) : Int × Int :=
  let fd := fileDiff src tgt
  let rd := rankDiff src tgt
  if fd = 0 then
    (0, signInt (-rd))
  else
    (signInt (-fd), 0)

def rookOffset (src tgt : Square) : Nat :=
  (fileDiff src tgt).natAbs + (rankDiff src tgt).natAbs

def bishopDelta (src tgt : Square) : Int × Int :=
  let fd := fileDiff src tgt
  let rd := rankDiff src tgt
  (signInt (-fd), signInt (-rd))

def bishopOffset (src tgt : Square) : Nat :=
  (fileDiff src tgt).natAbs

def squaresBetween (source target : Square) : List Square :=
  if isDiagonal source target then
    let fd := fileDiff source target
    let rd := rankDiff source target
    let steps := Int.natAbs fd
    let stepFile := signInt (-fd)
    let stepRank := signInt (-rd)
    if steps ≤ 1 then
      []
    else
      (List.range (steps - 1)).filterMap fun idx =>
        let step := Int.ofNat (idx + 1)
        squareFromInts (source.fileInt + stepFile * step) (source.rankInt + stepRank * step)
  else if isRookMove source target then
    let fd := fileDiff source target
    let rd := rankDiff source target
    let stepFile := signInt (-fd)
    let stepRank := signInt (-rd)
    let steps := Int.natAbs fd + Int.natAbs rd
    if steps ≤ 1 then
      []
    else
      (List.range (steps - 1)).filterMap fun idx =>
        let step := Int.ofNat (idx + 1)
        squareFromInts (source.fileInt + stepFile * step) (source.rankInt + stepRank * step)
  else
    []

theorem rook_move_straight {source target : Square} (h : isRookMove source target) :
    fileDiff source target = 0 ∨ rankDiff source target = 0 := by
  cases h.2 with
  | inl hcase => exact Or.inl hcase.left
  | inr hcase => exact Or.inr hcase.left

theorem knight_move_distance {source target : Square} (h : isKnightMove source target) :
    absInt (fileDiff source target) + absInt (rankDiff source target) = 3 := by
  cases h.2 with
  | inl hcase =>
    simp [hcase.left, hcase.right]
  | inr hcase =>
    simp [hcase.left, hcase.right]

theorem king_step_bounds {source target : Square} (h : isKingStep source target) :
    absInt (fileDiff source target) ≤ 1 ∧ absInt (rankDiff source target) ≤ 1 := by
  exact ⟨h.2.1, h.2.2⟩

theorem pawn_advance_direction {c : Color} {source target : Square} (h : isPawnAdvance c source target) :
    rankDiff source target = -pawnDirection c ∨ rankDiff source target = -2 * pawnDirection c :=
  h.2.2

theorem pawn_capture_offset {c : Color} {source target : Square} (h : isPawnCapture c source target) :
    absInt (fileDiff source target) = 1 :=
  h.2.1

theorem pawn_capture_forward {c : Color} {source target : Square} (h : isPawnCapture c source target) :
    rankDiff source target = -pawnDirection c :=
  h.2.2

-- ============================================================================
-- Bool/Prop Bridge Lemmas
-- ============================================================================

/-- Bidirectional equivalence between isKingStepBool and isKingStep -/
theorem isKingStepBool_eq_true_iff_isKingStep (source target : Square) :
    isKingStepBool source target = true ↔ isKingStep source target := by
  unfold isKingStepBool isKingStep
  constructor
  · intro h
    by_cases hEq : source = target
    · simp [hEq] at h
    · simp only [hEq, ↓reduceIte] at h
      constructor
      · exact hEq
      · split at h
        · rename_i hFile
          split at h
          · rename_i hRank
            exact ⟨hFile, hRank⟩
          · simp at h
        · simp at h
  · intro ⟨hNe, hFile, hRank⟩
    simp only [hNe, ↓reduceIte, hFile, hRank]

/-- Bidirectional equivalence between isKnightMoveBool and isKnightMove -/
theorem isKnightMoveBool_eq_true_iff_isKnightMove (source target : Square) :
    isKnightMoveBool source target = true ↔ isKnightMove source target := by
  unfold isKnightMoveBool isKnightMove
  constructor
  · intro h
    by_cases hEq : source = target
    · simp [hEq] at h
    · simp only [hEq, ↓reduceIte] at h
      constructor
      · exact hEq
      · split at h
        · rename_i hFile1
          split at h
          · rename_i hRank2
            exact Or.inl ⟨hFile1, hRank2⟩
          · simp at h
        · split at h
          · rename_i hNotFile1 hFile2
            split at h
            · rename_i hRank1
              exact Or.inr ⟨hFile2, hRank1⟩
            · simp at h
          · simp at h
  · intro ⟨hNe, hCases⟩
    simp only [hNe, ↓reduceIte]
    cases hCases with
    | inl hCase1 =>
      simp only [hCase1.1, ↓reduceIte, hCase1.2]
    | inr hCase2 =>
      have hNotFile1 : absInt (fileDiff source target) ≠ 1 := by
        simp only [hCase2.1]; decide
      simp only [↓reduceIte, hCase2.1, hCase2.2]
      decide

/-- Target in kingTargets iff isKingStep holds -/
theorem mem_kingTargets_iff (source target : Square) :
    target ∈ kingTargets source ↔ isKingStep source target := by
  unfold kingTargets
  simp only [List.mem_filter, Square.mem_all, true_and]
  exact isKingStepBool_eq_true_iff_isKingStep source target

/-- Target in knightTargets iff isKnightMove holds -/
theorem mem_knightTargets_iff (source target : Square) :
    target ∈ knightTargets source ↔ isKnightMove source target := by
  unfold knightTargets
  simp only [List.mem_filter, Square.mem_all, true_and]
  exact isKnightMoveBool_eq_true_iff_isKnightMove source target

-- ============================================================================
-- Helper Lemmas for Path Validation
-- ============================================================================

/--
When offset k is in range (0, N), then k - 1 is in List.range (N - 1).
This connects offset indexing to List.range enumeration.
-/
theorem range_membership_of_offset (N k : Nat) (h_pos : 0 < k) (h_lt : k < N) :
    k - 1 < N - 1 := by
  omega

/--
If idx ∈ List.range n, then idx < n (by definition of List.range).
Used to establish membership after indexing.
-/
theorem range_contains_iff {n idx : Nat} : idx ∈ List.range n ↔ idx < n := by
  simp [List.mem_range]

/--
Helper: List.range produces exactly [0, 1, ..., n-1].
-/
theorem list_range_eq (n : Nat) : List.range n = List.range n := rfl

/--
Helper: For a rook move, if k is a valid offset (0 < k < N), then k-1 is a valid index
for the List.range enumeration in squaresBetween.
-/
theorem rook_offset_range_membership (N k : Nat)
    (h_pos : 0 < k) (h_lt : k < N) :
    k - 1 ∈ List.range (N - 1) := by
  have : k - 1 < N - 1 := range_membership_of_offset N k h_pos h_lt
  exact List.mem_range.mpr this

/--
For a pawn two-step advance, the intermediate square exists.
Intermediate is at (src.file, src.rank + pawnDirection).
-/
theorem pawnTwoStep_intermediate_exists
    (h_adv : isPawnAdvance c src target)
    (h_two : rankDiff src target = -2 * pawnDirection c) :
    ∃ sq, squareFromInts src.fileInt (src.rankInt + pawnDirection c) = some sq := by
  unfold squareFromInts
  -- File is always valid: 0 ≤ fileInt < 8 from Fin 8
  have hf1 : (0 : Int) ≤ src.fileInt := by simp only [Square.fileInt]; exact Int.natCast_nonneg _
  have hf2 : src.fileInt < 8 := by
    simp only [Square.fileInt]
    exact Int.ofNat_lt.mpr src.file.isLt
  -- Rank validity depends on color
  have hr : 0 ≤ src.rankInt + pawnDirection c ∧ src.rankInt + pawnDirection c < 8 := by
    simp only [Square.rankInt, pawnDirection, rankDiff] at h_two ⊢
    have hs : src.rank.toNat < 8 := src.rank.isLt
    have ht : target.rank.toNat < 8 := target.rank.isLt
    -- Normalize Int.ofNat to coercion (↑) for omega consistency
    simp only [Int.ofNat_eq_natCast] at h_two ⊢
    cases c with
    | White => simp only [↓reduceIte] at h_two ⊢; omega
    | Black => omega
  simp only [hf1, hf2, hr.1, hr.2, and_self, ↓reduceIte]
  exact ⟨Square.mkUnsafe src.fileInt.toNat (src.rankInt + pawnDirection c).toNat, rfl⟩

/--
The intermediate square of a pawn two-step advance is in squaresBetween.

Proof sketch: A two-step pawn advance is a vertical rook move with |rankDiff| = 2.
The squaresBetween function for a 2-step vertical move returns exactly one intermediate
square, which is the one computed by squareFromInts at the intermediate rank.
-/
theorem pawnTwoStep_intermediate_in_squaresBetween
    (h_adv : isPawnAdvance c src target)
    (h_two : rankDiff src target = -2 * pawnDirection c)
    (sq : Square)
    (h_sq : squareFromInts src.fileInt (src.rankInt + pawnDirection c) = some sq) :
    sq ∈ squaresBetween src target := by
  -- Extract key facts from isPawnAdvance
  have h_neq : src ≠ target := h_adv.1
  have h_file_same : fileDiff src target = 0 := h_adv.2.1
  -- Show it's not diagonal: absInt(0) = 0 ≠ 2 = absInt(±2)
  have h_not_diag : ¬isDiagonal src target := by
    unfold isDiagonal
    intro ⟨_, h_eq⟩
    have h_abs_file : absInt (fileDiff src target) = 0 := by
      simp only [h_file_same, absInt]; decide
    have h_abs_rank : absInt (rankDiff src target) = 2 := by
      simp only [h_two, absInt, pawnDirection]
      cases c <;> decide
    rw [h_abs_file, h_abs_rank] at h_eq
    exact absurd h_eq (by decide : (0 : Int) ≠ 2)
  -- Show it's a rook move: fileDiff = 0 and rankDiff ≠ 0
  have h_rank_ne : rankDiff src target ≠ 0 := by
    simp only [h_two, pawnDirection]
    cases c <;> decide
  have h_rook : isRookMove src target := by
    unfold isRookMove
    exact ⟨h_neq, Or.inl ⟨h_file_same, h_rank_ne⟩⟩
  -- Compute the natAbs of rankDiff
  have h_rank_abs : (rankDiff src target).natAbs = 2 := by
    simp only [h_two, pawnDirection]
    cases c <;> native_decide
  -- Now unfold squaresBetween and work with the rook branch
  unfold squaresBetween
  simp only [h_not_diag, ↓reduceIte, h_rook]
  simp only [h_file_same, Int.natAbs_zero, Nat.zero_add, h_rank_abs]
  -- Since 2 > 1, we enter the filterMap branch with List.range 1 = [0]
  simp only [Nat.reduceLeDiff, ↓reduceIte]
  -- Compute stepRank = signInt(-rankDiff) = pawnDirection c
  have h_stepRank : signInt (-rankDiff src target) = pawnDirection c := by
    simp only [h_two, pawnDirection, signInt]
    cases c <;> decide
  -- The filterMap on [0] gives exactly our square
  -- First, simplify signInt (-0) = 0
  have h_signInt_neg_zero : signInt (-0) = 0 := by decide
  -- Show the filterMap result equals [sq]
  have h_result : List.filterMap
      (fun idx =>
        squareFromInts (src.fileInt + signInt (-0) * Int.ofNat (idx + 1))
          (src.rankInt + signInt (-rankDiff src target) * Int.ofNat (idx + 1)))
      (List.range (2 - 1)) = [sq] := by
    -- Simplify signInt (-0) = 0
    simp only [h_signInt_neg_zero, Int.zero_mul, Int.add_zero]
    -- List.range 1 = [0]
    simp only [show (2 - 1 : Nat) = 1 by decide, List.range_one]
    -- filterMap on singleton
    simp only [List.filterMap_cons, List.filterMap_nil]
    -- Rewrite signInt(-rankDiff) = pawnDirection c
    rw [h_stepRank]
    -- Simplify pawnDirection c * Int.ofNat 1 = pawnDirection c
    have h_mul_one : pawnDirection c * Int.ofNat 1 = pawnDirection c := by
      cases c <;> decide
    simp only [Nat.reduceAdd, h_mul_one]
    -- Now matches h_sq
    rw [h_sq]
  rw [h_result]
  exact List.mem_singleton_self sq

end Movement

end Chess
