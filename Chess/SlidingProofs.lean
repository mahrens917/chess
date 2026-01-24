import Chess.Rules
import Chess.PathValidationProofs

namespace Chess
namespace Rules

open Movement

set_option maxHeartbeats 800000

-- ============================================================================
-- Walk Function Lemmas
-- ============================================================================

/-- Walk unfolding equation: walk (s+1) unfolds to match on squareFromInts. -/
theorem walk_succ_eq (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (s : Nat) (acc : List Move) :
    slidingTargets.walk src p board color maxStep df dr (s + 1) acc =
    (match squareFromInts (src.fileInt + df * ↑(maxStep - s)) (src.rankInt + dr * ↑(maxStep - s)) with
     | none => acc
     | some target =>
         if isEmpty board target then
           slidingTargets.walk src p board color maxStep df dr s
             ({ piece := p, fromSq := src, toSq := target } :: acc)
         else if isEnemyAt board color target then
           { piece := p, fromSq := src, toSq := target, isCapture := true } :: acc
         else
           acc) := by rfl

/-- Walk preserves accumulator membership. -/
theorem walk_mem_acc (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (step : Nat) (acc : List Move) (m : Move)
    (hmem : m ∈ acc) :
    m ∈ slidingTargets.walk src p board color maxStep df dr step acc := by
  induction step generalizing acc with
  | zero => exact hmem
  | succ s ih =>
    rw [walk_succ_eq]
    cases h_sq : squareFromInts (src.fileInt + df * ↑(maxStep - s))
              (src.rankInt + dr * ↑(maxStep - s)) with
    | none => exact hmem
    | some target =>
      simp only
      split
      · exact ih _ (List.mem_cons_of_mem _ hmem)
      · split
        · exact List.mem_cons_of_mem _ hmem
        · exact hmem

/-- Walk step with empty square: continues walking with move added to accumulator. -/
private theorem walk_succ_empty_step (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (s : Nat) (acc : List Move) (sq : Square)
    (h_sq : squareFromInts (src.fileInt + df * ↑(maxStep - s))
              (src.rankInt + dr * ↑(maxStep - s)) = some sq)
    (h_empty : isEmpty board sq = true) :
    slidingTargets.walk src p board color maxStep df dr (s + 1) acc =
    slidingTargets.walk src p board color maxStep df dr s
      ({ piece := p, fromSq := src, toSq := sq } :: acc) := by
  rw [walk_succ_eq]
  show (match squareFromInts _ _ with
    | none => acc
    | some target => if isEmpty board target then _ else _) = _
  simp only [h_sq, h_empty, ↓reduceIte]

/-- Walk step with enemy square: adds capture move and stops. -/
private theorem walk_succ_enemy_step (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (s : Nat) (acc : List Move) (sq : Square)
    (h_sq : squareFromInts (src.fileInt + df * ↑(maxStep - s))
              (src.rankInt + dr * ↑(maxStep - s)) = some sq)
    (h_not_empty : isEmpty board sq = false)
    (h_enemy : isEnemyAt board color sq = true) :
    slidingTargets.walk src p board color maxStep df dr (s + 1) acc =
    { piece := p, fromSq := src, toSq := sq, isCapture := true } :: acc := by
  rw [walk_succ_eq]
  show (match squareFromInts _ _ with
    | none => acc
    | some target => if isEmpty board target then _ else _) = _
  simp only [h_sq, h_not_empty, Bool.false_eq_true, ↓reduceIte, h_enemy]

-- ============================================================================
-- Walk Completeness: Non-capture (empty target)
-- ============================================================================

/-- Walk generates a non-capture move to an empty target square when all
    intermediate squares are empty. -/
theorem walk_reaches_empty_general (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (step : Nat) (s_target : Nat) (acc : List Move) (target : Square)
    (h_step_gt : step > s_target)
    (h_target : squareFromInts (src.fileInt + df * ↑(maxStep - s_target))
                  (src.rankInt + dr * ↑(maxStep - s_target)) = some target)
    (h_empty : isEmpty board target = true)
    (h_path : ∀ k : Nat, s_target < k → k < step →
      ∃ sq, squareFromInts (src.fileInt + df * ↑(maxStep - k))
              (src.rankInt + dr * ↑(maxStep - k)) = some sq ∧
            isEmpty board sq = true) :
    { piece := p, fromSq := src, toSq := target } ∈
      slidingTargets.walk src p board color maxStep df dr step acc := by
  induction step generalizing acc with
  | zero => omega
  | succ s ih =>
    by_cases h_eq : s = s_target
    · subst h_eq
      rw [walk_succ_empty_step src p board color maxStep df dr s acc target h_target h_empty]
      apply walk_mem_acc
      exact @List.mem_cons_self Move _ _
    · have h_s_gt : s > s_target := by omega
      obtain ⟨sq, h_sq_eq, h_sq_empty⟩ := h_path s h_s_gt (by omega)
      rw [walk_succ_empty_step src p board color maxStep df dr s acc sq h_sq_eq h_sq_empty]
      exact ih _ h_s_gt (fun k hk_gt hk_lt => h_path k hk_gt (by omega))

-- ============================================================================
-- Walk Completeness: Capture (enemy-occupied target)
-- ============================================================================

/-- Walk generates a capture move to an enemy-occupied target square when all
    intermediate squares are empty. -/
theorem walk_reaches_enemy_general (src : Square) (p : Piece) (board : Board) (color : Color)
    (maxStep : Nat) (df dr : Int) (step : Nat) (s_target : Nat) (acc : List Move) (target : Square)
    (h_step_gt : step > s_target)
    (h_target : squareFromInts (src.fileInt + df * ↑(maxStep - s_target))
                  (src.rankInt + dr * ↑(maxStep - s_target)) = some target)
    (h_not_empty : isEmpty board target = false)
    (h_enemy : isEnemyAt board color target = true)
    (h_path : ∀ k : Nat, s_target < k → k < step →
      ∃ sq, squareFromInts (src.fileInt + df * ↑(maxStep - k))
              (src.rankInt + dr * ↑(maxStep - k)) = some sq ∧
            isEmpty board sq = true) :
    { piece := p, fromSq := src, toSq := target, isCapture := true } ∈
      slidingTargets.walk src p board color maxStep df dr step acc := by
  induction step generalizing acc with
  | zero => omega
  | succ s ih =>
    by_cases h_eq : s = s_target
    · subst h_eq
      rw [walk_succ_enemy_step src p board color maxStep df dr s acc target h_target h_not_empty h_enemy]
      exact @List.mem_cons_self Move _ _
    · have h_s_gt : s > s_target := by omega
      obtain ⟨sq, h_sq_eq, h_sq_empty⟩ := h_path s h_s_gt (by omega)
      rw [walk_succ_empty_step src p board color maxStep df dr s acc sq h_sq_eq h_sq_empty]
      exact ih _ h_s_gt (fun k hk_gt hk_lt => h_path k hk_gt (by omega))

-- ============================================================================
-- Connection to slidingTargets
-- ============================================================================

/-- If a move is in walk output for any accumulator, and the delta is in the list,
    then the move is in the slidingTargets result. -/
theorem mem_slidingTargets_of_walk (gs : GameState) (src : Square) (p : Piece)
    (deltas : List (Int × Int)) (df dr : Int) (m : Move)
    (h_delta : (df, dr) ∈ deltas)
    (h_any_acc : ∀ acc : List Move,
      m ∈ slidingTargets.walk src p gs.board p.color 7 df dr 7 acc) :
    m ∈ slidingTargets gs src p deltas := by
  unfold slidingTargets
  simp only
  -- Goal: m ∈ deltas.foldr (fun d acc => let (df, dr) := d; walk ...) []
  induction deltas with
  | nil => cases h_delta
  | cons d ds ih =>
    simp only [List.foldr]
    cases List.mem_cons.mp h_delta with
    | inl h_eq =>
      have h1 : d.1 = df := by rw [← h_eq]
      have h2 : d.2 = dr := by rw [← h_eq]
      simp only [h1, h2]
      exact h_any_acc _
    | inr h_in_ds =>
      have h_ih := ih h_in_ds
      exact walk_mem_acc _ _ _ _ _ _ _ _ _ m h_ih

-- ============================================================================
-- Target at end of ray
-- ============================================================================

/-- Key identity: signInt(-x) * (|x| : Int) = -x for x ≠ 0. -/
theorem signInt_mul_natAbs (x : Int) (hx : x ≠ 0) :
    signInt (-x) * (↑(Int.natAbs x) : Int) = -x := by
  unfold signInt
  by_cases h0 : -x = 0
  · exfalso; omega
  · by_cases hpos : -x > 0
    · simp only [h0, ↓reduceIte, hpos, Int.one_mul]; omega
    · simp only [h0, hpos, ↓reduceIte]; omega

/-- The target square is at offset rookOffset along the rookDelta direction. -/
theorem rookRay_target_valid (src tgt : Square) (h : isRookMove src tgt) :
    squareFromInts (src.fileInt + (rookDelta src tgt).1 * ↑(rookOffset src tgt))
      (src.rankInt + (rookDelta src tgt).2 * ↑(rookOffset src tgt)) = some tgt := by
  obtain ⟨h_ne, h_or⟩ := h
  cases h_or with
  | inl h_file =>
    obtain ⟨h_fd, h_rd⟩ := h_file
    have h_delta : rookDelta src tgt = (0, signInt (-rankDiff src tgt)) := by
      unfold rookDelta; simp [h_fd]
    rw [h_delta]
    simp only [Int.zero_mul, Int.add_zero]
    unfold rookOffset
    rw [h_fd]; simp only [Int.natAbs_zero, Nat.zero_add]
    have h_mul := signInt_mul_natAbs (rankDiff src tgt) h_rd
    have h_rank_eq : src.rankInt + signInt (-rankDiff src tgt) * ↑(Int.natAbs (rankDiff src tgt)) = tgt.rankInt := by
      rw [h_mul]; unfold rankDiff; omega
    rw [h_rank_eq]
    have h_file_eq : src.fileInt = tgt.fileInt := by
      unfold fileDiff at h_fd; omega
    rw [h_file_eq]
    exact squareFromInts_of_coords tgt
  | inr h_rank =>
    obtain ⟨h_rd, h_fd⟩ := h_rank
    have h_delta : rookDelta src tgt = (signInt (-fileDiff src tgt), 0) := by
      unfold rookDelta; simp [h_fd]
    rw [h_delta]
    simp only [Int.zero_mul, Int.add_zero]
    unfold rookOffset
    rw [h_rd]; simp only [Int.natAbs_zero, Nat.add_zero]
    have h_mul := signInt_mul_natAbs (fileDiff src tgt) h_fd
    have h_file_eq : src.fileInt + signInt (-fileDiff src tgt) * ↑(Int.natAbs (fileDiff src tgt)) = tgt.fileInt := by
      rw [h_mul]; unfold fileDiff; omega
    rw [h_file_eq]
    have h_rank_eq : src.rankInt = tgt.rankInt := by
      unfold rankDiff at h_rd; omega
    rw [h_rank_eq]
    exact squareFromInts_of_coords tgt

-- ============================================================================
-- PathClear to walk h_path connection
-- ============================================================================

/-- pathClear + rookRay properties imply the walk's path condition.
    For a rook move, the walk processes offsets 1 to rookOffset.
    The s_target = 7 - rookOffset, and intermediate offsets (1 to rookOffset-1)
    are in squaresBetween and thus empty. -/
theorem rookPathClear_walk_path (src tgt : Square) (board : Board)
    (h_rook : isRookMove src tgt) (h_clear : pathClear board src tgt = true) :
    ∀ k : Nat, 7 - rookOffset src tgt < k → k < 7 →
      ∃ sq, squareFromInts (src.fileInt + (rookDelta src tgt).1 * ↑(7 - k))
              (src.rankInt + (rookDelta src tgt).2 * ↑(7 - k)) = some sq ∧
            isEmpty board sq = true := by
  intro k hk_gt hk_lt
  have h_offset_pos : 0 < 7 - k := by omega
  have h_offset_lt : 7 - k < rookOffset src tgt := by
    have := rookOffset_le_7 src tgt h_rook
    omega
  have h_valid := rookRay_intermediate_valid src tgt h_rook (7 - k) h_offset_pos h_offset_lt
  obtain ⟨sq, hsq⟩ := h_valid
  refine ⟨sq, hsq, ?_⟩
  have h_in_between := rookRay_intermediate_in_squaresBetween src tgt h_rook (7 - k) h_offset_pos h_offset_lt
  have h_sq_in := h_in_between sq hsq
  unfold pathClear at h_clear
  exact List.all_eq_true.mp h_clear sq h_sq_in

-- ============================================================================
-- Main Rook Completeness for slidingTargets
-- ============================================================================

/-- A rook move with clear path produces a move in slidingTargets.
    Handles both capture and non-capture cases based on destination. -/
theorem rook_in_slidingTargets (gs : GameState) (src tgt : Square) (p : Piece)
    (h_rook : isRookMove src tgt)
    (h_clear : pathClear gs.board src tgt = true)
    (h_dest : destinationFriendlyFreeProp gs { piece := p, fromSq := src, toSq := tgt }) :
    (isEmpty gs.board tgt = true →
      { piece := p, fromSq := src, toSq := tgt } ∈
        slidingTargets gs src p [(1, 0), (-1, 0), (0, 1), (0, -1)]) ∧
    (isEmpty gs.board tgt = false → isEnemyAt gs.board p.color tgt = true →
      { piece := p, fromSq := src, toSq := tgt, isCapture := true } ∈
        slidingTargets gs src p [(1, 0), (-1, 0), (0, 1), (0, -1)]) := by
  have h_delta := rookDelta_in_deltas src tgt h_rook
  have h_offset_pos := rookOffset_pos src tgt h_rook
  have h_offset_le := rookOffset_le_7 src tgt h_rook
  have h_target := rookRay_target_valid src tgt h_rook
  have h_path := rookPathClear_walk_path src tgt gs.board h_rook h_clear
  have h_s_lt : 7 - rookOffset src tgt < 7 := by omega
  -- Convert h_target to use 7 - (7 - rookOffset) form for walk compatibility
  have h_nat_eq : 7 - (7 - rookOffset src tgt) = rookOffset src tgt := by omega
  have h_target' : squareFromInts (src.fileInt + (rookDelta src tgt).1 * ↑(7 - (7 - rookOffset src tgt)))
      (src.rankInt + (rookDelta src tgt).2 * ↑(7 - (7 - rookOffset src tgt))) = some tgt := by
    have h_cast_eq : (↑(7 - (7 - rookOffset src tgt)) : Int) = ↑(rookOffset src tgt) := by
      congr 1
    rw [h_cast_eq]
    exact h_target
  constructor
  · intro h_empty
    apply mem_slidingTargets_of_walk gs src p _ (rookDelta src tgt).1 (rookDelta src tgt).2
    · exact h_delta
    · intro acc
      exact walk_reaches_empty_general src p gs.board p.color 7
        (rookDelta src tgt).1 (rookDelta src tgt).2 7 (7 - rookOffset src tgt) acc tgt
        h_s_lt h_target' h_empty h_path
  · intro h_not_empty h_enemy
    apply mem_slidingTargets_of_walk gs src p _ (rookDelta src tgt).1 (rookDelta src tgt).2
    · exact h_delta
    · intro acc
      exact walk_reaches_enemy_general src p gs.board p.color 7
        (rookDelta src tgt).1 (rookDelta src tgt).2 7 (7 - rookOffset src tgt) acc tgt
        h_s_lt h_target' h_not_empty h_enemy h_path

-- ============================================================================
-- Bishop Target at end of ray
-- ============================================================================

/-- The target square is at offset bishopOffset along the bishopDelta direction. -/
theorem bishopRay_target_valid (src tgt : Square) (h : isDiagonal src tgt) :
    squareFromInts (src.fileInt + (bishopDelta src tgt).1 * ↑(bishopOffset src tgt))
      (src.rankInt + (bishopDelta src tgt).2 * ↑(bishopOffset src tgt)) = some tgt := by
  have hfd_ne := isDiagonal_fileDiff_ne_zero src tgt h
  have hrd_ne := isDiagonal_rankDiff_ne_zero src tgt h
  have h_natabs_eq := isDiagonal_natAbs_eq src tgt h
  have h_delta : bishopDelta src tgt = (signInt (-fileDiff src tgt), signInt (-rankDiff src tgt)) := rfl
  rw [h_delta]
  -- bishopOffset = |fd|
  have h_mul_fd := signInt_mul_natAbs (fileDiff src tgt) hfd_ne
  have h_mul_rd := signInt_mul_natAbs (rankDiff src tgt) hrd_ne
  have h_file_eq : src.fileInt + signInt (-fileDiff src tgt) * ↑(bishopOffset src tgt) = tgt.fileInt := by
    -- bishopOffset = natAbs fd
    show src.fileInt + signInt (-fileDiff src tgt) * ↑(Int.natAbs (fileDiff src tgt)) = tgt.fileInt
    rw [h_mul_fd]; unfold fileDiff; omega
  have h_rank_eq : src.rankInt + signInt (-rankDiff src tgt) * ↑(bishopOffset src tgt) = tgt.rankInt := by
    -- bishopOffset = |fd| = |rd|, so substitute |rd|
    have h_cast_eq : (↑(bishopOffset src tgt) : Int) = ↑(Int.natAbs (rankDiff src tgt)) := by
      unfold bishopOffset; exact congrArg (Int.ofNat ·) h_natabs_eq
    rw [h_cast_eq, h_mul_rd]; unfold rankDiff; omega
  rw [h_file_eq, h_rank_eq]
  exact squareFromInts_of_coords tgt

-- ============================================================================
-- Bishop PathClear to walk path connection
-- ============================================================================

/-- pathClear + bishopRay properties imply the walk's path condition. -/
theorem bishopPathClear_walk_path (src tgt : Square) (board : Board)
    (h_bishop : isDiagonal src tgt) (h_clear : pathClear board src tgt = true) :
    ∀ k : Nat, 7 - bishopOffset src tgt < k → k < 7 →
      ∃ sq, squareFromInts (src.fileInt + (bishopDelta src tgt).1 * ↑(7 - k))
              (src.rankInt + (bishopDelta src tgt).2 * ↑(7 - k)) = some sq ∧
            isEmpty board sq = true := by
  intro k hk_gt hk_lt
  have h_offset_pos : 0 < 7 - k := by omega
  have h_offset_lt : 7 - k < bishopOffset src tgt := by
    have := bishopOffset_le_7 src tgt h_bishop
    omega
  have h_valid := bishopRay_intermediate_valid src tgt h_bishop (7 - k) h_offset_pos h_offset_lt
  obtain ⟨sq, hsq⟩ := h_valid
  refine ⟨sq, hsq, ?_⟩
  have h_in_between := bishopRay_intermediate_in_squaresBetween src tgt h_bishop (7 - k) h_offset_pos h_offset_lt
  have h_sq_in := h_in_between sq hsq
  unfold pathClear at h_clear
  exact List.all_eq_true.mp h_clear sq h_sq_in

-- ============================================================================
-- Main Bishop Completeness for slidingTargets
-- ============================================================================

/-- A bishop move with clear path produces a move in slidingTargets. -/
theorem bishop_in_slidingTargets (gs : GameState) (src tgt : Square) (p : Piece)
    (h_bishop : isDiagonal src tgt)
    (h_clear : pathClear gs.board src tgt = true)
    (h_dest : destinationFriendlyFreeProp gs { piece := p, fromSq := src, toSq := tgt }) :
    (isEmpty gs.board tgt = true →
      { piece := p, fromSq := src, toSq := tgt } ∈
        slidingTargets gs src p [(1, 1), (-1, -1), (1, -1), (-1, 1)]) ∧
    (isEmpty gs.board tgt = false → isEnemyAt gs.board p.color tgt = true →
      { piece := p, fromSq := src, toSq := tgt, isCapture := true } ∈
        slidingTargets gs src p [(1, 1), (-1, -1), (1, -1), (-1, 1)]) := by
  have h_delta := bishopDelta_in_deltas src tgt h_bishop
  have h_offset_pos := bishopOffset_pos src tgt h_bishop
  have h_offset_le := bishopOffset_le_7 src tgt h_bishop
  have h_target := bishopRay_target_valid src tgt h_bishop
  have h_path := bishopPathClear_walk_path src tgt gs.board h_bishop h_clear
  have h_s_lt : 7 - bishopOffset src tgt < 7 := by omega
  have h_nat_eq : 7 - (7 - bishopOffset src tgt) = bishopOffset src tgt := by omega
  have h_target' : squareFromInts (src.fileInt + (bishopDelta src tgt).1 * ↑(7 - (7 - bishopOffset src tgt)))
      (src.rankInt + (bishopDelta src tgt).2 * ↑(7 - (7 - bishopOffset src tgt))) = some tgt := by
    have h_cast_eq : (↑(7 - (7 - bishopOffset src tgt)) : Int) = ↑(bishopOffset src tgt) := by
      congr 1
    rw [h_cast_eq]
    exact h_target
  constructor
  · intro h_empty
    apply mem_slidingTargets_of_walk gs src p _ (bishopDelta src tgt).1 (bishopDelta src tgt).2
    · exact h_delta
    · intro acc
      exact walk_reaches_empty_general src p gs.board p.color 7
        (bishopDelta src tgt).1 (bishopDelta src tgt).2 7 (7 - bishopOffset src tgt) acc tgt
        h_s_lt h_target' h_empty h_path
  · intro h_not_empty h_enemy
    apply mem_slidingTargets_of_walk gs src p _ (bishopDelta src tgt).1 (bishopDelta src tgt).2
    · exact h_delta
    · intro acc
      exact walk_reaches_enemy_general src p gs.board p.color 7
        (bishopDelta src tgt).1 (bishopDelta src tgt).2 7 (7 - bishopOffset src tgt) acc tgt
        h_s_lt h_target' h_not_empty h_enemy h_path

-- ============================================================================
-- Queen Completeness for slidingTargets
-- ============================================================================

def queenDeltas : List (Int × Int) :=
  [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)]

private theorem rook_mem_queen_deltas {d : Int × Int}
    (h : d ∈ ([(1, 0), (-1, 0), (0, 1), (0, -1)] : List (Int × Int))) :
    d ∈ queenDeltas := by
  have : d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1) := by
    simpa using h
  unfold queenDeltas
  rcases this with rfl | rfl | rfl | rfl <;> decide

private theorem bishop_mem_queen_deltas {d : Int × Int}
    (h : d ∈ ([(1, 1), (-1, -1), (1, -1), (-1, 1)] : List (Int × Int))) :
    d ∈ queenDeltas := by
  have : d = (1, 1) ∨ d = (-1, -1) ∨ d = (1, -1) ∨ d = (-1, 1) := by
    simpa using h
  unfold queenDeltas
  rcases this with rfl | rfl | rfl | rfl <;> decide

/-- A queen move with clear path produces a move in slidingTargets. -/
theorem queen_in_slidingTargets (gs : GameState) (src tgt : Square) (p : Piece)
    (h_queen : isQueenMove src tgt)
    (h_clear : pathClear gs.board src tgt = true)
    (h_dest : destinationFriendlyFreeProp gs { piece := p, fromSq := src, toSq := tgt }) :
    (isEmpty gs.board tgt = true →
      { piece := p, fromSq := src, toSq := tgt } ∈
        slidingTargets gs src p queenDeltas) ∧
    (isEmpty gs.board tgt = false → isEnemyAt gs.board p.color tgt = true →
      { piece := p, fromSq := src, toSq := tgt, isCapture := true } ∈
        slidingTargets gs src p queenDeltas) := by
  unfold isQueenMove at h_queen
  cases h_queen with
  | inl h_rook =>
    have h_delta := rook_mem_queen_deltas (rookDelta_in_deltas src tgt h_rook)
    have h_offset_pos := rookOffset_pos src tgt h_rook
    have h_offset_le := rookOffset_le_7 src tgt h_rook
    have h_target := rookRay_target_valid src tgt h_rook
    have h_path := rookPathClear_walk_path src tgt gs.board h_rook h_clear
    have h_s_lt : 7 - rookOffset src tgt < 7 := by omega
    have h_target' : squareFromInts (src.fileInt + (rookDelta src tgt).1 * ↑(7 - (7 - rookOffset src tgt)))
        (src.rankInt + (rookDelta src tgt).2 * ↑(7 - (7 - rookOffset src tgt))) = some tgt := by
      have h_cast_eq : (↑(7 - (7 - rookOffset src tgt)) : Int) = ↑(rookOffset src tgt) := by
        congr 1; omega
      rw [h_cast_eq]; exact h_target
    constructor
    · intro h_empty
      apply mem_slidingTargets_of_walk gs src p _ (rookDelta src tgt).1 (rookDelta src tgt).2
      · exact h_delta
      · intro acc
        exact walk_reaches_empty_general src p gs.board p.color 7
          (rookDelta src tgt).1 (rookDelta src tgt).2 7 (7 - rookOffset src tgt) acc tgt
          h_s_lt h_target' h_empty h_path
    · intro h_not_empty h_enemy
      apply mem_slidingTargets_of_walk gs src p _ (rookDelta src tgt).1 (rookDelta src tgt).2
      · exact h_delta
      · intro acc
        exact walk_reaches_enemy_general src p gs.board p.color 7
          (rookDelta src tgt).1 (rookDelta src tgt).2 7 (7 - rookOffset src tgt) acc tgt
          h_s_lt h_target' h_not_empty h_enemy h_path
  | inr h_bishop =>
    have h_delta := bishop_mem_queen_deltas (bishopDelta_in_deltas src tgt h_bishop)
    have h_offset_pos := bishopOffset_pos src tgt h_bishop
    have h_offset_le := bishopOffset_le_7 src tgt h_bishop
    have h_target := bishopRay_target_valid src tgt h_bishop
    have h_path := bishopPathClear_walk_path src tgt gs.board h_bishop h_clear
    have h_s_lt : 7 - bishopOffset src tgt < 7 := by omega
    have h_target' : squareFromInts (src.fileInt + (bishopDelta src tgt).1 * ↑(7 - (7 - bishopOffset src tgt)))
        (src.rankInt + (bishopDelta src tgt).2 * ↑(7 - (7 - bishopOffset src tgt))) = some tgt := by
      have h_cast_eq : (↑(7 - (7 - bishopOffset src tgt)) : Int) = ↑(bishopOffset src tgt) := by
        congr 1; omega
      rw [h_cast_eq]; exact h_target
    constructor
    · intro h_empty
      apply mem_slidingTargets_of_walk gs src p _ (bishopDelta src tgt).1 (bishopDelta src tgt).2
      · exact h_delta
      · intro acc
        exact walk_reaches_empty_general src p gs.board p.color 7
          (bishopDelta src tgt).1 (bishopDelta src tgt).2 7 (7 - bishopOffset src tgt) acc tgt
          h_s_lt h_target' h_empty h_path
    · intro h_not_empty h_enemy
      apply mem_slidingTargets_of_walk gs src p _ (bishopDelta src tgt).1 (bishopDelta src tgt).2
      · exact h_delta
      · intro acc
        exact walk_reaches_enemy_general src p gs.board p.color 7
          (bishopDelta src tgt).1 (bishopDelta src tgt).2 7 (7 - bishopOffset src tgt) acc tgt
          h_s_lt h_target' h_not_empty h_enemy h_path

end Rules
end Chess
