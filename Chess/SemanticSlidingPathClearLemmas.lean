import Init.Omega
import Chess.SemanticSlidingGeometryLemmas
import Chess.SlidingProofs

namespace Chess
namespace Rules

open Movement

set_option maxHeartbeats 4000000

-- ============================================================================
-- Path Clearance Proofs for Sliding Pieces
-- ============================================================================

-- ============================================================================
-- Walk intermediate emptiness lemma
-- ============================================================================

/-- Walk produces moves where all intermediate offsets are empty.
    If m ∈ walk step acc and m ∉ acc, then there exists K (the offset of m.toSq)
    such that all offsets between the start of this walk's range and K were empty. -/
private theorem walk_fresh_move_intermediates_empty
    (src : Square) (p : Piece) (board : Board) (color : Color) (maxStep : Nat)
    (df dr : Int) :
    ∀ (step : Nat) (acc : List Move) (m : Move),
    step ≤ maxStep →
    m ∈ slidingTargets.walk src p board color maxStep df dr step acc →
    m ∉ acc →
    ∃ K : Nat, maxStep - step < K ∧ K ≤ maxStep ∧
      squareFromInts (src.fileInt + df * ↑K) (src.rankInt + dr * ↑K) = some m.toSq ∧
      m.fromSq = src ∧
      (∀ j : Nat, maxStep - step < j → j < K →
        ∃ sq, squareFromInts (src.fileInt + df * ↑j) (src.rankInt + dr * ↑j) = some sq ∧
              isEmpty board sq = true) := by
  intro step
  induction step with
  | zero =>
    intro acc m _ hMem hNotAcc
    simp [slidingTargets.walk] at hMem
    exact absurd hMem hNotAcc
  | succ s ih =>
    intro acc m hLe hMem hNotAcc
    rw [walk_succ_eq] at hMem
    cases hSq : squareFromInts (src.fileInt + df * ↑(maxStep - s))
                  (src.rankInt + dr * ↑(maxStep - s)) with
    | none =>
      simp [hSq] at hMem
      exact absurd hMem hNotAcc
    | some target =>
      simp only [hSq] at hMem
      by_cases hEmpty : isEmpty board target = true
      · -- Current square is empty, walk continues
        simp only [hEmpty, ↓reduceIte] at hMem
        by_cases hInExtAcc : m ∈ ({ piece := p, fromSq := src, toSq := target } :: acc)
        · rcases List.mem_cons.mp hInExtAcc with hEq | hInAcc
          · -- m is the move to target (offset maxStep - s)
            subst hEq
            exact ⟨maxStep - s, by omega, by omega, hSq, rfl,
              fun j hj_gt hj_lt => by omega⟩
          · exact absurd hInAcc hNotAcc
        · -- m is freshly produced by recursive walk
          have hLe' : s ≤ maxStep := Nat.le_of_succ_le hLe
          obtain ⟨K, hK_gt, hK_le, hK_sq, hK_from, hK_inter⟩ :=
            ih ({ piece := p, fromSq := src, toSq := target } :: acc) m hLe' hMem hInExtAcc
          exact ⟨K, by omega, hK_le, hK_sq, hK_from, fun j hj_gt hj_lt => by
            by_cases hj_eq : j = maxStep - s
            · subst hj_eq; exact ⟨target, hSq, hEmpty⟩
            · exact hK_inter j (by omega) hj_lt⟩
      · -- Current square is not empty
        simp only [hEmpty, Bool.false_eq_true, ↓reduceIte] at hMem
        by_cases hEnemy : isEnemyAt board color target = true
        · -- Enemy capture at current offset
          simp only [hEnemy, ↓reduceIte] at hMem
          rcases List.mem_cons.mp hMem with hEq | hInAcc
          · subst hEq
            exact ⟨maxStep - s, by omega, by omega, hSq, rfl,
              fun j hj_gt hj_lt => by omega⟩
          · exact absurd hInAcc hNotAcc
        · simp only [hEnemy, ↓reduceIte] at hMem
          exact absurd hMem hNotAcc

-- ============================================================================
-- Tracing slidingTargets to a specific walk
-- ============================================================================

/-- Any move in slidingTargets comes from a specific walk call. -/
private theorem slidingTargets_exists_walk
    (gs : GameState) (src : Square) (p : Piece)
    (deltas : List (Int × Int)) (m : Move) :
    m ∈ slidingTargets gs src p deltas →
    ∃ df dr : Int, (df, dr) ∈ deltas ∧
      ∃ acc, m ∈ slidingTargets.walk src p gs.board p.color 7 df dr 7 acc ∧ m ∉ acc := by
  unfold slidingTargets
  simp only
  intro hMem
  induction deltas with
  | nil => simp [List.foldr] at hMem
  | cons d ds ih =>
    simp only [List.foldr] at hMem
    let acc := ds.foldr (fun d' acc' =>
      slidingTargets.walk src p gs.board p.color 7 d'.1 d'.2 7 acc') []
    by_cases hInAcc : m ∈ acc
    · obtain ⟨df, dr, hDelta, acc', hWalk, hNotAcc'⟩ := ih hInAcc
      exact ⟨df, dr, List.mem_cons_of_mem _ hDelta, acc', hWalk, hNotAcc'⟩
    · exact ⟨d.1, d.2, List.mem_cons_self, acc, hMem, hInAcc⟩

-- ============================================================================
-- Algebraic helpers
-- ============================================================================

/-- signInt(d * K) = d when d ∈ {-1, 0, 1} and K > 0. -/
private theorem signInt_unit_mul_pos {d : Int} {K : Nat} (hK : 0 < K)
    (hUnit : d = -1 ∨ d = 0 ∨ d = 1) :
    signInt (d * ↑K) = d := by
  unfold signInt
  rcases hUnit with rfl | rfl | rfl <;> simp <;> omega

/-- For a rook delta (df, dr) and target at offset K from src,
    fileDiff = -df*K and rankDiff = -dr*K. -/
private theorem walk_target_fileDiff {src tgt : Square} {df dr : Int} {K : Nat}
    (hSq : squareFromInts (src.fileInt + df * ↑K) (src.rankInt + dr * ↑K) = some tgt) :
    fileDiff src tgt = -(df * ↑K) := by
  have hFile := squareFromInts_fileInt _ _ tgt hSq
  unfold fileDiff
  omega

private theorem walk_target_rankDiff {src tgt : Square} {df dr : Int} {K : Nat}
    (hSq : squareFromInts (src.fileInt + df * ↑K) (src.rankInt + dr * ↑K) = some tgt) :
    rankDiff src tgt = -(dr * ↑K) := by
  have hRank := squareFromInts_rankInt _ _ tgt hSq
  unfold rankDiff
  omega

-- ============================================================================
-- squaresBetween elements come from walk intermediates
-- ============================================================================

/-- For a rook delta, |fileDiff| + |rankDiff| = K. -/
private theorem rook_delta_offset {src tgt : Square} {df dr : Int} {K : Nat}
    (hK : 0 < K)
    (hSq : squareFromInts (src.fileInt + df * ↑K) (src.rankInt + dr * ↑K) = some tgt)
    (hDelta : isRookDelta (df, dr)) :
    (fileDiff src tgt).natAbs + (rankDiff src tgt).natAbs = K := by
  rw [walk_target_fileDiff hSq, walk_target_rankDiff hSq]
  unfold isRookDelta at hDelta
  rcases hDelta with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

/-- For a bishop delta, |fileDiff| = K. -/
private theorem bishop_delta_offset {src tgt : Square} {df dr : Int} {K : Nat}
    (hK : 0 < K)
    (hSq : squareFromInts (src.fileInt + df * ↑K) (src.rankInt + dr * ↑K) = some tgt)
    (hDelta : isBishopDelta (df, dr)) :
    (fileDiff src tgt).natAbs = K := by
  rw [walk_target_fileDiff hSq]
  unfold isBishopDelta at hDelta
  rcases hDelta with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

/-- For a rook delta with target at offset K, squaresBetween src tgt consists of
    squares at offsets 1..K-1 using the same delta. -/
private theorem squaresBetween_rook_eq_intermediates {src tgt : Square} {df dr : Int} {K : Nat}
    (hK : 0 < K)
    (hSq : squareFromInts (src.fileInt + df * ↑K) (src.rankInt + dr * ↑K) = some tgt)
    (hDelta : isRookDelta (df, dr)) :
    squaresBetween src tgt =
      if K ≤ 1 then []
      else (List.range (K - 1)).filterMap fun idx =>
        squareFromInts (src.fileInt + df * Int.ofNat (idx + 1))
                       (src.rankInt + dr * Int.ofNat (idx + 1)) := by
  have hRook := isRookMove_of_coords hSq hK hDelta
  have hNotDiag := rook_not_diagonal_prop hRook
  unfold squaresBetween
  rw [if_neg hNotDiag, if_pos hRook]
  have hSteps := rook_delta_offset hK hSq hDelta
  have hFD := walk_target_fileDiff hSq
  have hRD := walk_target_rankDiff hSq
  have hSignF : signInt (-fileDiff src tgt) = df := by
    rw [hFD]; simp only [Int.neg_neg]
    exact signInt_unit_mul_pos hK (by
      unfold isRookDelta at hDelta
      rcases hDelta with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp)
  have hSignR : signInt (-rankDiff src tgt) = dr := by
    rw [hRD]; simp only [Int.neg_neg]
    exact signInt_unit_mul_pos hK (by
      unfold isRookDelta at hDelta
      rcases hDelta with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp)
  simp only [hSteps, hSignF, hSignR]

/-- For a bishop delta with target at offset K, squaresBetween src tgt consists of
    squares at offsets 1..K-1 using the same delta. -/
private theorem squaresBetween_bishop_eq_intermediates {src tgt : Square} {df dr : Int} {K : Nat}
    (hK : 0 < K)
    (hSq : squareFromInts (src.fileInt + df * ↑K) (src.rankInt + dr * ↑K) = some tgt)
    (hDelta : isBishopDelta (df, dr)) :
    squaresBetween src tgt =
      if K ≤ 1 then []
      else (List.range (K - 1)).filterMap fun idx =>
        squareFromInts (src.fileInt + df * Int.ofNat (idx + 1))
                       (src.rankInt + dr * Int.ofNat (idx + 1)) := by
  have hDiag := isDiagonal_of_coords hSq hK hDelta
  unfold squaresBetween
  rw [if_pos hDiag]
  have hSteps := bishop_delta_offset hK hSq hDelta
  have hFD := walk_target_fileDiff hSq
  have hRD := walk_target_rankDiff hSq
  have hSignF : signInt (-fileDiff src tgt) = df := by
    rw [hFD]; simp only [Int.neg_neg]
    exact signInt_unit_mul_pos hK (by
      unfold isBishopDelta at hDelta
      rcases hDelta with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp)
  have hSignR : signInt (-rankDiff src tgt) = dr := by
    rw [hRD]; simp only [Int.neg_neg]
    exact signInt_unit_mul_pos hK (by
      unfold isBishopDelta at hDelta
      rcases hDelta with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp)
  simp only [hSteps, hSignF, hSignR]

-- ============================================================================
-- Main pathClear proof for unit deltas
-- ============================================================================

/-- Helper: isEmpty board sq = true implies (board : Board → Square → Option Piece) sq = none -/
private theorem isEmpty_implies_none {board : Board} {sq : Square}
    (h : isEmpty board sq = true) : board sq = none := by
  unfold isEmpty at h; exact of_decide_eq_true h

/-- For a move produced by slidingTargets with unit deltas that are all rook or bishop deltas,
    pathClear holds. -/
theorem mem_slidingTargets_pathClear_of_unit_deltas
    (gs : GameState) (src : Square) (p : Piece)
    (deltas : List (Int × Int)) (m : Move)
    (hAllUnit : ∀ d ∈ deltas, isRookDelta d ∨ isBishopDelta d) :
    m ∈ slidingTargets gs src p deltas →
    pathClear gs.board src m.toSq = true := by
  intro hMem
  -- Trace to a specific walk
  obtain ⟨df, dr, hDeltaMem, acc, hWalkMem, hNotAcc⟩ :=
    slidingTargets_exists_walk gs src p deltas m hMem
  -- Get intermediate emptiness from walk
  obtain ⟨K, hK_gt, hK_le, hK_sq, hK_from, hK_inter⟩ :=
    walk_fresh_move_intermediates_empty src p gs.board p.color 7 df dr
      7 acc m (by omega) hWalkMem hNotAcc
  -- The offset K starts from > 7 - 7 = 0, so K > 0
  have hK_pos : 0 < K := by omega
  -- Determine if rook or bishop delta
  have hDeltaType := hAllUnit (df, dr) hDeltaMem
  -- Show pathClear
  unfold pathClear
  rw [List.all_eq_true]
  intro sq hSqMem
  -- Show board sq = none by connecting squaresBetween to walk intermediates
  rcases hDeltaType with hRook | hBishop
  · -- Rook delta case
    rw [squaresBetween_rook_eq_intermediates hK_pos hK_sq hRook] at hSqMem
    by_cases hK1 : K ≤ 1
    · simp [hK1] at hSqMem
    · simp only [hK1, ↓reduceIte] at hSqMem
      rw [List.mem_filterMap] at hSqMem
      obtain ⟨idx, hIdx_range, hIdx_sq⟩ := hSqMem
      rw [List.mem_range] at hIdx_range
      have hJ_lt : idx + 1 < K := by omega
      have hJ_gt : 7 - 7 < idx + 1 := by omega
      obtain ⟨sq', hSq'_eq, hSq'_empty⟩ := hK_inter (idx + 1) hJ_gt hJ_lt
      -- squareFromInts is deterministic: hIdx_sq and hSq'_eq give sq = sq'
      -- Note: ↑(idx+1) and Int.ofNat (idx+1) are definitionally equal
      have hEq : sq = sq' := by
        have h := hIdx_sq.symm.trans hSq'_eq
        cases h; rfl
      subst hEq
      exact decide_eq_true_eq.mpr (isEmpty_implies_none hSq'_empty)
  · -- Bishop delta case
    rw [squaresBetween_bishop_eq_intermediates hK_pos hK_sq hBishop] at hSqMem
    by_cases hK1 : K ≤ 1
    · simp [hK1] at hSqMem
    · simp only [hK1, ↓reduceIte] at hSqMem
      rw [List.mem_filterMap] at hSqMem
      obtain ⟨idx, hIdx_range, hIdx_sq⟩ := hSqMem
      rw [List.mem_range] at hIdx_range
      have hJ_lt : idx + 1 < K := by omega
      have hJ_gt : 7 - 7 < idx + 1 := by omega
      obtain ⟨sq', hSq'_eq, hSq'_empty⟩ := hK_inter (idx + 1) hJ_gt hJ_lt
      have hEq : sq = sq' := by
        have h := hIdx_sq.symm.trans hSq'_eq
        cases h; rfl
      subst hEq
      exact decide_eq_true_eq.mpr (isEmpty_implies_none hSq'_empty)

-- ============================================================================
-- Specific theorems for rook, bishop, queen
-- ============================================================================

private theorem rook_deltas_are_unit :
    ∀ d ∈ [(1, 0), (-1, 0), (0, 1), (0, -1)],
    isRookDelta d ∨ isBishopDelta d := by
  intro d hd
  left
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> unfold isRookDelta <;> decide

private theorem bishop_deltas_are_unit :
    ∀ d ∈ [(1, 1), (-1, -1), (1, -1), (-1, 1)],
    isRookDelta d ∨ isBishopDelta d := by
  intro d hd
  right
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> unfold isBishopDelta <;> decide

private theorem queen_deltas_are_unit :
    ∀ d ∈ [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)],
    isRookDelta d ∨ isBishopDelta d := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (left; unfold isRookDelta; decide)
    | (right; unfold isBishopDelta; decide)

theorem mem_slidingTargets_pathClear_rook
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hRook : p.pieceType = PieceType.Rook) :
    m ∈ pieceTargets gs src p →
    pathClear gs.board src m.toSq = true := by
  intro hMem
  unfold pieceTargets at hMem
  simp only [hRook] at hMem
  exact mem_slidingTargets_pathClear_of_unit_deltas gs src p
    [(1, 0), (-1, 0), (0, 1), (0, -1)] m rook_deltas_are_unit hMem

theorem mem_slidingTargets_pathClear_bishop
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hBishop : p.pieceType = PieceType.Bishop) :
    m ∈ pieceTargets gs src p →
    pathClear gs.board src m.toSq = true := by
  intro hMem
  unfold pieceTargets at hMem
  simp only [hBishop] at hMem
  exact mem_slidingTargets_pathClear_of_unit_deltas gs src p
    [(1, 1), (-1, -1), (1, -1), (-1, 1)] m bishop_deltas_are_unit hMem

theorem mem_slidingTargets_pathClear_queen
    (gs : GameState) (src : Square) (p : Piece) (m : Move)
    (hQueen : p.pieceType = PieceType.Queen) :
    m ∈ pieceTargets gs src p →
    pathClear gs.board src m.toSq = true := by
  intro hMem
  unfold pieceTargets at hMem
  simp only [hQueen] at hMem
  exact mem_slidingTargets_pathClear_of_unit_deltas gs src p
    [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)] m
    queen_deltas_are_unit hMem

end Rules
end Chess
