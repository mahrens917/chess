import Chess.Rules
import Chess.AttackSpec
import Chess.KkDeadPositionProofs
import Chess.KMinorSpecificEndgameInvariants

namespace Chess
namespace Rules

open PieceType Color

-- ============================================================================
-- POSITION VALIDITY PREDICATES
-- ============================================================================

/-- A position has valid king configuration if there's at most one king per color. -/
def hasValidKings (b : Board) : Prop :=
  (∀ sq1 sq2, (∃ p1, b sq1 = some p1 ∧ p1.pieceType = PieceType.King ∧ p1.color = Color.White) →
              (∃ p2, b sq2 = some p2 ∧ p2.pieceType = PieceType.King ∧ p2.color = Color.White) →
              sq1 = sq2) ∧
  (∀ sq1 sq2, (∃ p1, b sq1 = some p1 ∧ p1.pieceType = PieceType.King ∧ p1.color = Color.Black) →
              (∃ p2, b sq2 = some p2 ∧ p2.pieceType = PieceType.King ∧ p2.color = Color.Black) →
              sq1 = sq2)

/-- Two squares are adjacent if they differ by at most 1 in both file and rank. -/
def squaresAdjacent (sq1 sq2 : Square) : Bool :=
  let fd := if sq1.fileInt ≥ sq2.fileInt then sq1.fileInt - sq2.fileInt else sq2.fileInt - sq1.fileInt
  let rd := if sq1.rankInt ≥ sq2.rankInt then sq1.rankInt - sq2.rankInt else sq2.rankInt - sq1.rankInt
  fd ≤ 1 && rd ≤ 1 && (fd > 0 || rd > 0)

/-- In a legal position, the two kings are never adjacent.
    This is required by FIDE chess rules - a king cannot move into check. -/
def kingsNotAdjacent (b : Board) : Prop :=
  ∀ sq1 sq2,
    (∃ p1, b sq1 = some p1 ∧ p1.pieceType = PieceType.King ∧ p1.color = Color.White) →
    (∃ p2, b sq2 = some p2 ∧ p2.pieceType = PieceType.King ∧ p2.color = Color.Black) →
    squaresAdjacent sq1 sq2 = false

/-- A legal position has valid kings that are not adjacent. -/
def isLegalPosition (b : Board) : Prop :=
  hasValidKings b ∧ kingsNotAdjacent b

-- ============================================================================
-- Helper predicates for material configurations
-- ============================================================================

def whiteHasOnlyKing (gs : GameState) : Prop :=
  ∀ sq : Square, ∀ p : Piece,
    gs.board sq = some p → p.color = Color.White → p.pieceType = PieceType.King

def blackHasOnlyKing (gs : GameState) : Prop :=
  ∀ sq : Square, ∀ p : Piece,
    gs.board sq = some p → p.color = Color.Black → p.pieceType = PieceType.King

def whiteHasOnlyKingKnight (gs : GameState) : Prop :=
  ∀ sq : Square, ∀ p : Piece,
    gs.board sq = some p → p.color = Color.White →
      p.pieceType = PieceType.King ∨ p.pieceType = PieceType.Knight

def whiteHasOnlyKingBishop (gs : GameState) : Prop :=
  ∀ sq : Square, ∀ p : Piece,
    gs.board sq = some p → p.color = Color.White →
      p.pieceType = PieceType.King ∨ p.pieceType = PieceType.Bishop

def bishopsOnSameColorSquares (gs : GameState) : Prop :=
  ∃ (isLight : Bool),
    ∀ sq : Square, ∀ p : Piece,
      gs.board sq = some p → p.pieceType = PieceType.Bishop →
        squareIsLight sq = isLight

/-- Helper: A board has only kings if countNonKingPieces = 0 -/
def boardHasOnlyKings (b : Board) : Prop :=
  ∀ sq p, b sq = some p → p.pieceType = PieceType.King

/-- Helper for foldl: count non-kings starting from accumulator -/
private def countNonKingsFrom (b : Board) (squares : List Square) (acc : Nat) : Nat :=
  squares.foldl (fun a sq =>
    match b sq with
    | some p => if p.pieceType ≠ PieceType.King then a + 1 else a
    | none => a) acc

/-- Helper: foldl is monotonically increasing.
    Proof: Each step either increments the accumulator or leaves it unchanged,
    so the final result is at least the initial value. -/
private theorem countNonKingsFrom_ge_acc (b : Board) (squares : List Square) (acc : Nat) :
    countNonKingsFrom b squares acc ≥ acc := by
  unfold countNonKingsFrom
  induction squares generalizing acc with
  | nil => simp only [List.foldl_nil]; exact Nat.le_refl acc
  | cons sq rest ih =>
    simp only [List.foldl_cons]
    -- Each step increments or preserves acc, so result >= acc
    have h_step : (match b sq with
      | some p => if p.pieceType ≠ PieceType.King then acc + 1 else acc
      | none => acc) ≥ acc := by
      split
      · split
        · exact Nat.le_add_right acc 1
        · exact Nat.le_refl acc
      · exact Nat.le_refl acc
    have h_rest := @ih (match b sq with
      | some p => if p.pieceType ≠ PieceType.King then acc + 1 else acc
      | none => acc)
    exact Nat.le_trans h_step h_rest

/-- Helper: if foldl result is acc, then no non-kings were found (iff version).
    The forward direction uses contrapositive: if a non-king exists, the foldl
    must increment at that square, giving result > acc.
    The reverse direction: if all pieces are kings, no increment ever happens.

    PROOF NOTE: This is a technical lemma about the foldl computation.
    The forward direction requires showing that if a non-king exists, the
    accumulator must have been incremented at that point.
    The reverse direction is straightforward by induction. -/
private theorem countNonKingsFrom_eq_acc_iff (b : Board) (squares : List Square) (acc : Nat) :
    countNonKingsFrom b squares acc = acc ↔
    ∀ sq ∈ squares, ∀ p, b sq = some p → p.pieceType = PieceType.King := by
  constructor
  · -- Forward: countNonKingsFrom = acc → all pieces are kings
    -- By contrapositive: if a non-king exists, the count would be > acc
    intro h sq hMem p hp
    -- Prove by contradiction using decidability
    by_cases h_king : p.pieceType = PieceType.King
    · exact h_king
    · -- p is not a king, we derive a contradiction
      exfalso
      -- Split squares into pre ++ [sq] ++ suf
      obtain ⟨pre, suf, hsplit⟩ := List.mem_iff_append.mp hMem
      rw [hsplit] at h
      -- Unfold foldl for pre ++ [sq] ++ suf
      unfold countNonKingsFrom at h
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
      -- After pre, acc' = countNonKingsFrom b pre acc ≥ acc
      let acc' := List.foldl (fun a sq' =>
        match b sq' with
        | some p' => if p'.pieceType ≠ PieceType.King then a + 1 else a
        | none => a) acc pre
      have h_acc'_ge : acc' ≥ acc := countNonKingsFrom_ge_acc b pre acc
      -- At sq with non-king p, we increment: acc'' = acc' + 1
      have h_at_sq : (match b sq with
        | some p' => if p'.pieceType ≠ PieceType.King then acc' + 1 else acc'
        | none => acc') = acc' + 1 := by
        have : b sq = some p := hp
        simp only [this, if_pos h_king]
      -- After suf, result ≥ acc' + 1 by monotonicity
      have h_suf_ge : List.foldl (fun a sq' =>
          match b sq' with
          | some p' => if p'.pieceType ≠ PieceType.King then a + 1 else a
          | none => a) (acc' + 1) suf ≥ acc' + 1 := countNonKingsFrom_ge_acc b suf (acc' + 1)
      -- Combine: derive foldl f (acc'+1) suf = acc, then contradiction
      have h_key : List.foldl (fun a sq' =>
          match b sq' with
          | some p' => if p'.pieceType ≠ PieceType.King then a + 1 else a
          | none => a) (acc' + 1) suf = acc := by
        rw [← h_at_sq]; exact h
      omega
  · -- Reverse: all pieces are kings → countNonKingsFrom = acc
    intro h
    induction squares generalizing acc with
    | nil =>
      unfold countNonKingsFrom
      rfl
    | cons sq rest ih =>
      unfold countNonKingsFrom
      simp only [List.foldl_cons]
      -- The step at sq: since all pieces are kings, no increment
      have h_sq : ∀ p, b sq = some p → p.pieceType = PieceType.King := by
        intro p hp
        exact h sq (by simp) p hp
      have h_step : (match b sq with
        | some p => if p.pieceType ≠ PieceType.King then acc + 1 else acc
        | none => acc) = acc := by
        split
        case h_1 p heq =>
          have hk : p.pieceType = PieceType.King := h_sq p heq
          simp [hk]
        case h_2 => rfl
      rw [h_step]
      apply ih
      intro sq' hMem p hp
      exact h sq' (by simp [hMem]) p hp

/-- Helper: countNonKingPieces = 0 iff all pieces are kings.
    Proof relies on the characterization of countNonKingsFrom. -/
-- Helper: countNonKingPieces equals countNonKingsFrom with initial accumulator 0
private theorem countNonKingPieces_eq_countNonKingsFrom (gs : GameState) :
    countNonKingPieces gs = countNonKingsFrom gs.board allSquares 0 := by
  unfold countNonKingPieces countNonKingsFrom
  rfl

theorem countNonKingPieces_zero_iff_onlyKings (gs : GameState) :
    countNonKingPieces gs = 0 ↔ boardHasOnlyKings gs.board := by
  constructor
  · -- 0 non-kings → all pieces are kings
    intro h sq p hp
    -- Rewrite using the helper and axiom
    rw [countNonKingPieces_eq_countNonKingsFrom] at h
    have hAxiom := (countNonKingsFrom_eq_acc_iff gs.board allSquares 0).mp h
    exact hAxiom sq (Square.mem_all sq) p hp
  · -- all pieces are kings → 0 non-kings
    intro h
    rw [countNonKingPieces_eq_countNonKingsFrom]
    apply (countNonKingsFrom_eq_acc_iff gs.board allSquares 0).mpr
    intro sq _hMem p hp
    exact h sq p hp

/-- Helper: countNonKingsFrom = 0 iff all pieces are kings (for any board) -/
private theorem countNonKingsFrom_zero_iff_onlyKings (b : Board) :
    countNonKingsFrom b allSquares 0 = 0 ↔ boardHasOnlyKings b := by
  constructor
  · intro h sq p hp
    have hAxiom := (countNonKingsFrom_eq_acc_iff b allSquares 0).mp h
    exact hAxiom sq (Square.mem_all sq) p hp
  · intro h
    apply (countNonKingsFrom_eq_acc_iff b allSquares 0).mpr
    intro sq _hMem p hp
    exact h sq p hp

-- finalizeResult_board and GameState.playMove_board are imported from KkDeadPositionProofs

/-- Helper: Updating a board preserves the only-kings property if we add a king or none.
    Proof: If sq' = sq, the piece comes from mp (which is a king by h_piece).
    If sq' /= sq, the piece comes from the original board (king by h_board). -/
theorem board_update_preserves_onlyKings (b : Board) (sq : Square) (mp : Option Piece)
    (h_board : boardHasOnlyKings b)
    (h_piece : forall p, mp = some p -> p.pieceType = PieceType.King) :
    boardHasOnlyKings (b.update sq mp) := by
  unfold boardHasOnlyKings at *
  intro sq' p' hp'
  -- The coercion means (b.update sq mp) sq' = (b.update sq mp).get sq'
  -- We case split on whether sq' = sq
  by_cases heq : sq' = sq
  · -- Case sq' = sq: the piece at sq' is mp
    subst heq
    have hp'_eq : (b.update sq' mp).get sq' = mp := Board.update_eq b sq' mp
    -- hp' : (b.update sq' mp) sq' = some p' means (b.update sq' mp).get sq' = some p'
    simp only at hp'
    rw [hp'_eq] at hp'
    exact h_piece p' hp'
  · -- Case sq' ≠ sq: the piece at sq' comes from original board
    have hp'_ne : (b.update sq mp).get sq' = b.get sq' := Board.update_ne b sq mp heq
    simp only at hp'
    rw [hp'_ne] at hp'
    exact h_board sq' p' hp'

/-- Helper: Updating to none trivially preserves only-kings -/
theorem board_update_none_preserves_onlyKings (b : Board) (sq : Square)
    (h_board : boardHasOnlyKings b) :
    boardHasOnlyKings (b.update sq none) := by
  apply board_update_preserves_onlyKings b sq none h_board
  intro p hp
  cases hp

/-- Helper: Adding a piece from a king-only board preserves only-kings -/
theorem board_update_from_onlyKings (b : Board) (sq_from sq_to : Square)
    (h_board : boardHasOnlyKings b) :
    boardHasOnlyKings (b.update sq_to (b sq_from)) := by
  apply board_update_preserves_onlyKings b sq_to (b sq_from) h_board
  intro p hp
  exact h_board sq_from p hp

/-- Helper: Castle handling preserves only-kings property -/
theorem castle_preserves_onlyKings (b : Board) (m : Move)
    (h_board : boardHasOnlyKings b) :
    boardHasOnlyKings (
      if m.isCastle then
        match m.castleRookFrom, m.castleRookTo with
        | some rFrom, some rTo =>
            (b.update rFrom none).update rTo (b rFrom)
        | _, _ => b
      else b
    ) := by
  split
  case isTrue =>
    split
    case h_1 rFrom rTo _ _ =>
      have h1 : boardHasOnlyKings (b.update rFrom none) :=
        board_update_none_preserves_onlyKings b rFrom h_board
      apply board_update_preserves_onlyKings _ rTo (b rFrom) h1
      intro p hp
      exact h_board rFrom p hp
    all_goals exact h_board
  case isFalse =>
    exact h_board

/-- Helper: En passant handling preserves only-kings property -/
theorem enpassant_preserves_onlyKings (b : Board) (m : Move) (captureSq : Square)
    (h_board : boardHasOnlyKings b) :
    boardHasOnlyKings (if m.isEnPassant then b.update captureSq none else b) := by
  split
  case isTrue => exact board_update_none_preserves_onlyKings b captureSq h_board
  case isFalse => exact h_board

/-- Any king move (without promotion) from a king-only position results in a king-only position.
    Since movePiece places m.piece at m.toSq, and m.piece is a king with no promotion,
    no non-king pieces are created.

    **Hypotheses**:
    - h: Only kings are on the board
    - h_king: The move involves a king piece
    - h_no_promo: No promotion (kings don't promote)

    **Justification**: movePiece performs these board operations:
    1. Potentially clears en passant capture square (removes piece or no-op)
    2. Potentially moves rook for castling (king moves don't castle)
    3. Clears fromSq and places promotedPiece at toSq

    Since promotedPiece returns the original piece when promotion=none, and the
    original piece is a king (h_king), only kings are placed on the board.
    All other operations either remove pieces or are no-ops. -/
theorem kingOnly_preserved_by_moves (gs : GameState) (m : Move)
    (h : countNonKingPieces gs = 0)
    (h_king : m.piece.pieceType = PieceType.King)
    (h_no_promo : m.promotion = none) :
    countNonKingPieces (GameState.playMove gs m) = 0 := by
  -- Convert h to boardHasOnlyKings
  have h_only : boardHasOnlyKings gs.board :=
    (countNonKingPieces_zero_iff_onlyKings gs).mp h
  -- The result board is (gs.movePiece m).board
  -- We need to show boardHasOnlyKings (gs.movePiece m).board
  -- Then use countNonKingPieces_zero_iff_onlyKings in reverse

  -- First, show the promoted piece is a king (since no promotion and piece is king)
  have h_promo_piece : (GameState.promotedPiece gs m).pieceType = PieceType.King := by
    unfold GameState.promotedPiece
    simp [h_no_promo, h_king]

  -- The board after movePiece only has kings
  have h_board_only : boardHasOnlyKings (gs.movePiece m).board := by
    unfold GameState.movePiece
    -- The final board is: (boardAfterCastle.update m.fromSq none).update m.toSq (some movingPiece)
    -- where movingPiece = gs.promotedPiece m (a king)
    -- boardAfterCastle is either boardAfterCapture or has rook moves (but rook must be king in king-only)
    -- boardAfterCapture is either gs.board or gs.board with en passant square cleared

    -- Let's build up the chain of board transformations
    let movingPiece := GameState.promotedPiece gs m
    let captureSq := enPassantCaptureSquare m |>.getD m.toSq
    let boardAfterCapture := if m.isEnPassant then gs.board.update captureSq none else gs.board
    let boardAfterCastle :=
      if m.isCastle then
        match m.castleRookFrom, m.castleRookTo with
        | some rFrom, some rTo =>
            let cleared := boardAfterCapture.update rFrom none
            cleared.update rTo (boardAfterCapture rFrom)
        | _, _ => boardAfterCapture
      else
        boardAfterCapture
    let board' := (boardAfterCastle.update m.fromSq none).update m.toSq (some movingPiece)

    -- Show boardAfterCapture has only kings
    have h_cap : boardHasOnlyKings boardAfterCapture := by
      unfold boardAfterCapture
      split
      case isTrue => exact board_update_none_preserves_onlyKings gs.board captureSq h_only
      case isFalse => exact h_only

    -- Show boardAfterCastle has only kings
    have h_castle : boardHasOnlyKings boardAfterCastle := by
      unfold boardAfterCastle
      split
      case isTrue =>
        split
        case h_1 rFrom rTo _ _ =>
          have h1 : boardHasOnlyKings (boardAfterCapture.update rFrom none) :=
            board_update_none_preserves_onlyKings boardAfterCapture rFrom h_cap
          apply board_update_preserves_onlyKings _ rTo (boardAfterCapture rFrom) h1
          intro p hp
          exact h_cap rFrom p hp
        all_goals exact h_cap
      case isFalse =>
        exact h_cap

    -- Show the final board has only kings
    have h_final : boardHasOnlyKings board' := by
      unfold board'
      have h_cleared : boardHasOnlyKings (boardAfterCastle.update m.fromSq none) :=
        board_update_none_preserves_onlyKings boardAfterCastle m.fromSq h_castle
      apply board_update_preserves_onlyKings _ m.toSq (some movingPiece) h_cleared
      intro p hp
      cases hp
      exact h_promo_piece

    -- The constructed board' equals the actual result
    exact h_final

  -- Use the equivalence to get countNonKingPieces = 0
  -- We use GameState.playMove_board which shows (GameState.playMove gs m).board = (gs.movePiece m).board
  -- Then countNonKingPieces on that GameState counts non-kings on (gs.movePiece m).board

  -- Key insight: countNonKingPieces only looks at the .board field
  -- So if we can show the board of (GameState.playMove gs m) equals (gs.movePiece m).board,
  -- and that board has only kings, we're done.

  -- Use the fact that countNonKingPieces depends only on the board
  have h_count : countNonKingPieces (GameState.playMove gs m) =
      countNonKingsFrom (GameState.playMove gs m).board allSquares 0 := by
    rfl

  -- Use the playMove_board theorem
  have h_eq : (GameState.playMove gs m).board = (gs.movePiece m).board :=
    GameState.playMove_board gs m

  rw [h_count, h_eq]
  exact (countNonKingsFrom_zero_iff_onlyKings (gs.movePiece m).board).mpr h_board_only

/-- Helper: isKingStep (Prop) implies squaresAdjacent (Bool).
    Both encode Chebyshev distance = 1 but in different representations. -/
private theorem isKingStep_implies_squaresAdjacent (sq1 sq2 : Square)
    (h : Movement.isKingStep sq1 sq2) : squaresAdjacent sq1 sq2 = true := by
  obtain ⟨h_ne, h_fd, h_rd⟩ := h
  unfold squaresAdjacent Square.fileInt Square.rankInt
  simp only [File.toNat, Rank.toNat, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  unfold Movement.absInt Movement.fileDiff Square.fileInt at h_fd
  unfold Movement.absInt Movement.rankDiff Square.rankInt at h_rd
  simp only [File.toNat, Rank.toNat] at h_fd h_rd
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · split <;> split at h_fd <;> omega
  · split <;> split at h_rd <;> omega
  · -- fd > 0 ∨ rd > 0; if both ≤ 0 then sq1 = sq2, contradicting h_ne
    rcases Decidable.em ((if (Int.ofNat ↑sq1.file : Int) ≥ (Int.ofNat ↑sq2.file : Int)
        then (Int.ofNat ↑sq1.file : Int) - (Int.ofNat ↑sq2.file : Int)
        else (Int.ofNat ↑sq2.file : Int) - (Int.ofNat ↑sq1.file : Int)) > 0) with h_pos | h_npos
    · exact Or.inl h_pos
    · right
      have h_file_eq : sq1.fileInt = sq2.fileInt := by
        unfold Square.fileInt; simp only [File.toNat]; split at h_npos <;> omega
      have h_ne_rank : sq1.rankInt ≠ sq2.rankInt := by
        intro h_eq; exact h_ne (Square.ext_fileInt_rankInt h_file_eq h_eq)
      unfold Square.rankInt at h_ne_rank; simp only [Rank.toNat] at h_ne_rank
      split <;> omega

/-- Helper: squaresAdjacent is symmetric. -/
private theorem squaresAdjacent_symm (sq1 sq2 : Square) :
    squaresAdjacent sq1 sq2 = squaresAdjacent sq2 sq1 := by
  simp only [squaresAdjacent, Square.fileInt, Square.rankInt, File.toNat, Rank.toNat]
  have h_fd : (if (Int.ofNat ↑sq1.file : Int) ≥ (Int.ofNat ↑sq2.file : Int)
      then (Int.ofNat ↑sq1.file : Int) - (Int.ofNat ↑sq2.file : Int)
      else (Int.ofNat ↑sq2.file : Int) - (Int.ofNat ↑sq1.file : Int)) =
    (if (Int.ofNat ↑sq2.file : Int) ≥ (Int.ofNat ↑sq1.file : Int)
      then (Int.ofNat ↑sq2.file : Int) - (Int.ofNat ↑sq1.file : Int)
      else (Int.ofNat ↑sq1.file : Int) - (Int.ofNat ↑sq2.file : Int)) := by
    split <;> split <;> omega
  have h_rd : (if (Int.ofNat ↑sq1.rank : Int) ≥ (Int.ofNat ↑sq2.rank : Int)
      then (Int.ofNat ↑sq1.rank : Int) - (Int.ofNat ↑sq2.rank : Int)
      else (Int.ofNat ↑sq2.rank : Int) - (Int.ofNat ↑sq1.rank : Int)) =
    (if (Int.ofNat ↑sq2.rank : Int) ≥ (Int.ofNat ↑sq1.rank : Int)
      then (Int.ofNat ↑sq2.rank : Int) - (Int.ofNat ↑sq1.rank : Int)
      else (Int.ofNat ↑sq1.rank : Int) - (Int.ofNat ↑sq2.rank : Int)) := by
    split <;> split <;> omega
  simp only [h_fd, h_rd]

/-- Helper: In a king-only board with non-adjacent kings, no one is in check.
    The only pieces that can attack are kings, and kings attack via adjacency.
    Since kings are not adjacent (by h_legal), inCheck = false. -/
private theorem inCheckStatus_false_of_onlyKings_legal (gs : GameState)
    (h : countNonKingPieces gs = 0)
    (h_legal : isLegalPosition gs.board) :
    inCheckStatus gs = false := by
  have h_only := (countNonKingPieces_zero_iff_onlyKings gs).mp h
  have ⟨_, h_not_adj⟩ := h_legal
  unfold inCheckStatus
  rw [Bool.eq_false_iff]
  intro h_chk
  have h_ex := (inCheck_eq_true_iff_exists_attacker gs.board gs.toMove).mp h_chk
  obtain ⟨kingSq, hKingSq, sq, p, _, hAt, hColor, hAtk⟩ := h_ex
  -- p is a king (from boardHasOnlyKings)
  have h_king : p.pieceType = PieceType.King := h_only sq p hAt
  -- attacksSpec for King reduces to isKingStep
  have h_step : Movement.isKingStep sq kingSq := by
    unfold attacksSpec at hAtk
    simp [h_king] at hAtk
    exact hAtk
  -- isKingStep implies squaresAdjacent
  have h_adj : squaresAdjacent sq kingSq = true :=
    isKingStep_implies_squaresAdjacent sq kingSq h_step
  -- Extract king at kingSq from kingSquare definition
  unfold kingSquare at hKingSq
  have h_pred := List.find?_some hKingSq
  -- h_pred : pred kingSq = true, case split on board content
  cases h_ks : gs.board kingSq with
  | none => simp [h_ks] at h_pred
  | some pk =>
    simp [h_ks] at h_pred
    -- h_pred : pk.pieceType = King ∧ pk.color = gs.toMove
    cases hc : gs.toMove with
    | White =>
      have h_white : ∃ p1, gs.board kingSq = some p1 ∧ p1.pieceType = PieceType.King ∧ p1.color = Color.White :=
        ⟨pk, h_ks, h_pred.1, h_pred.2.trans hc⟩
      have h_black : ∃ p2, gs.board sq = some p2 ∧ p2.pieceType = PieceType.King ∧ p2.color = Color.Black :=
        ⟨p, hAt, h_king, hColor.trans (by rw [hc]; rfl)⟩
      have h_not := h_not_adj kingSq sq h_white h_black
      rw [squaresAdjacent_symm kingSq sq] at h_not
      exact absurd h_adj (Bool.eq_false_iff.mp h_not)
    | Black =>
      have h_white : ∃ p1, gs.board sq = some p1 ∧ p1.pieceType = PieceType.King ∧ p1.color = Color.White :=
        ⟨p, hAt, h_king, hColor.trans (by rw [hc]; rfl)⟩
      have h_black : ∃ p2, gs.board kingSq = some p2 ∧ p2.pieceType = PieceType.King ∧ p2.color = Color.Black :=
        ⟨pk, h_ks, h_pred.1, h_pred.2.trans hc⟩
      have h_not := h_not_adj sq kingSq h_white h_black
      exact absurd h_adj (Bool.eq_false_iff.mp h_not)

/-- Helper theorem: With only kings on the board and a legal position, checkmate is impossible.
    Kings cannot attack each other (chess rule: king must be at least 1 square away).
    Since there are no other pieces, no other unit can deliver check.
    Therefore, inCheck is always false, and checkmate is impossible.

    **Hypotheses**:
    - h: Only kings are on the board
    - h_legal: The position is legal (kings not adjacent)

    **Justification**: isCheckmate requires inCheck = true.
    The inCheck function checks if any piece attacks the king. With only kings on the board:
    1. The only potential attackers are kings (from h)
    2. Kings attack via isKingStepBool which requires adjacency
    3. kingsNotAdjacent holds (from h_legal)
    Therefore inCheck = false for either side, making isCheckmate = false.

    Note: applyMoveSequence gs [] = gs, so this reduces to isCheckmate gs = false. -/
theorem kingVsKing_no_checkmate (gs : GameState)
    (h : countNonKingPieces gs = 0)
    (h_legal : isLegalPosition gs.board) :
    ¬(Rules.isCheckmate (applyMoveSequence gs [])) := by
  -- applyMoveSequence gs [] = gs
  simp only [applyMoveSequence]
  -- isCheckmate = inCheckStatus && noLegalMoves
  -- We show inCheckStatus = false, so isCheckmate = false
  have h_not_in_check : inCheckStatus gs = false :=
    inCheckStatus_false_of_onlyKings_legal gs h h_legal
  unfold isCheckmate
  simp [h_not_in_check]

-- Theorem 1: King vs King is a dead position
-- Strategy: Use the KkInv infrastructure from KkDeadPositionProofs which proves
-- that the king-only invariant is preserved by legal moves and no checkmate is reachable.
theorem king_vs_king_dead (gs : GameState)
    (h : countNonKingPieces gs = 0)
    (h_legal : isLegalPosition gs.board)
    (h_wk : ∃ sq, gs.board sq = some (kingPiece Color.White))
    (h_bk : ∃ sq, gs.board sq = some (kingPiece Color.Black)) :
    isDeadPosition gs := by
  -- Bridge to KingsOnly: find the king squares and show all others are empty
  obtain ⟨wk, hwk⟩ := h_wk
  obtain ⟨bk, hbk⟩ := h_bk
  have h_only := (countNonKingPieces_zero_iff_onlyKings gs).mp h
  have ⟨h_valid, _⟩ := h_legal
  -- Show wk ≠ bk (they have different colors)
  have h_ne : wk ≠ bk := by
    intro heq
    subst heq
    rw [hwk] at hbk
    exact absurd hbk (by simp [kingPiece])
  -- Show all other squares are empty
  have h_empty : ∀ sq, sq ≠ wk → sq ≠ bk → gs.board sq = none := by
    intro sq hne_wk hne_bk
    cases h_sq : gs.board sq with
    | none => rfl
    | some p =>
      have h_king := h_only sq p h_sq
      cases hc : p.color with
      | White =>
        exact absurd (h_valid.1 sq wk ⟨p, h_sq, h_king, hc⟩ ⟨_, hwk, rfl, rfl⟩) hne_wk
      | Black =>
        exact absurd (h_valid.2 sq bk ⟨p, h_sq, h_king, hc⟩ ⟨_, hbk, rfl, rfl⟩) hne_bk
  -- Construct KingsOnly
  have hKO : KingsOnly gs.board wk bk := by
    refine ⟨hwk, hbk, h_ne, ?_⟩
    intro sq hne1 hne2
    exact h_empty sq hne1 hne2
  -- Show kings not adjacent
  have h_not_adj : ¬ Movement.isKingStep wk bk := by
    intro h_step
    have h_adj : squaresAdjacent wk bk = true :=
      isKingStep_implies_squaresAdjacent wk bk h_step
    have ⟨_, h_kings_apart⟩ := h_legal
    have h_false := h_kings_apart wk bk
      ⟨_, hwk, rfl, rfl⟩
      ⟨_, hbk, rfl, rfl⟩
    rw [h_false] at h_adj
    exact absurd h_adj (by decide)
  -- Use the proved KkInv dead position theorem
  exact isDeadPosition_of_KingsOnly gs wk bk hKO h_not_adj

/-- Endgame theorem: King + Knight vs King cannot reach checkmate.
    This is a fundamental chess endgame fact. A knight and king lack the
    coordination and range to trap an enemy king. The knight can only reach
    at most 8 squares at L-shape distance, insufficient for mating patterns.

    **Justification**: A lone knight cannot deliver checkmate because:
    1. Knight attacks at most 8 squares (L-shape pattern)
    2. For checkmate, all escape squares of the defending king must be covered
    3. A king has up to 8 adjacent squares to potentially escape to
    4. The attacking king cannot help because it must stay at least 2 squares away
       (moving adjacent would be illegal - king can't move into check)
    5. Therefore, there's always at least one escape square for the defending king

    This is a well-known chess endgame fact, verified by chess engine analysis.

    PROOF COMPLEXITY NOTE: A full formal proof requires:
    1. Induction on move sequences showing the material configuration is preserved
    2. For each position, showing that if the defending king is in check, it has
       an escape square not attacked by the knight or attacking king
    3. This involves geometric analysis of knight move patterns vs king adjacency
    4. The proof would need ~100s of lines handling all corner/edge cases -/
-- Theorem 2: King + Knight vs King is a dead position
-- Strategy: Use the KknOrKkInv infrastructure which proves:
-- 1. The K+N or K invariant is preserved through legal moves
-- 2. No position satisfying the invariant can be checkmate
/-- K+N vs K is a dead position when we have exactly the required pieces. -/
theorem king_knight_vs_king_dead' (gs : GameState)
    (hInv : KknInv gs) :
    isDeadPosition gs :=
  KknOrKkInv.isDeadPosition gs (Or.inl hInv)

-- Original version with weaker hypotheses (requires bridging to KknInv)
theorem king_knight_vs_king_dead (gs : GameState)
    (h_white : whiteHasOnlyKingKnight gs)
    (h_black : blackHasOnlyKing gs)
    (h_legal : isLegalPosition gs.board)
    (h_wk : ∃ sq, gs.board sq = some (kingPiece Color.White))
    (h_bk : ∃ sq, gs.board sq = some (kingPiece Color.Black))
    (h_knight : ∃ sq mp, gs.board sq = some mp ∧ mp.pieceType = PieceType.Knight) :
    isDeadPosition gs := by
  -- Bridge to KknInv
  obtain ⟨wk, hwk⟩ := h_wk
  obtain ⟨bk, hbk⟩ := h_bk
  obtain ⟨nsq, np, hnp, hKnight⟩ := h_knight
  -- Show wk ≠ bk
  have h_ne_wk_bk : wk ≠ bk := by
    intro heq; subst heq; rw [hwk] at hbk
    exact absurd hbk (by simp [kingPiece])
  -- Determine knight color
  have h_knight_white : np.color = Color.White := by
    -- The knight must be white (black only has kings)
    by_contra h_not_white
    have h_black_piece : np.color = Color.Black := by
      cases np.color <;> simp_all
    have h_king := h_black nsq np hnp h_black_piece
    rw [h_king] at hKnight
    cases hKnight
  -- Show nsq ≠ wk and nsq ≠ bk
  have h_nsq_ne_wk : nsq ≠ wk := by
    intro heq; subst heq; rw [hnp] at hwk
    have : np = kingPiece Color.White := Option.some.inj hwk
    rw [this] at hKnight; simp [kingPiece] at hKnight
  have h_nsq_ne_bk : nsq ≠ bk := by
    intro heq; subst heq; rw [hnp] at hbk
    have : np = kingPiece Color.Black := Option.some.inj hbk
    rw [this] at hKnight; simp [kingPiece] at hKnight
  -- Show all other squares are empty
  have h_empty : ∀ sq, sq ≠ wk → sq ≠ bk → sq ≠ nsq → gs.board sq = none := by
    intro sq hne_wk hne_bk hne_nsq
    cases h_sq : gs.board sq with
    | none => rfl
    | some p =>
      cases hc : p.color with
      | White =>
        have htype := h_white sq p h_sq hc
        rcases htype with hK | hN
        · -- It's a white king, must be wk
          have := h_legal.1 sq wk ⟨p, h_sq, hK, hc⟩ ⟨_, hwk, rfl, rfl⟩
          exact absurd this hne_wk
        · -- It's a white knight, must be nsq
          -- Two white knights are equal (Piece is determined by pieceType and color)
          have h_eq : p = np := by
            -- p and np have same pieceType (Knight) and same color (White)
            have hp_type : p.pieceType = PieceType.Knight := hN
            have hp_color : p.color = Color.White := hc
            have hnp_type : np.pieceType = PieceType.Knight := hKnight
            have hnp_color : np.color = Color.White := h_knight_white
            -- Piece is a structure with only pieceType and color fields
            cases p; cases np
            simp only [Piece.mk.injEq] at *
            exact ⟨hp_type.trans hnp_type.symm, hp_color.trans hnp_color.symm⟩
          have h_sq_eq : sq = nsq := by
            -- If p = np and gs.board sq = some p and gs.board nsq = some np
            -- then sq = nsq follows from injectivity of board lookup
            rw [h_eq] at h_sq
            exact Option.some.inj (Eq.trans h_sq.symm hnp)
          exact absurd h_sq_eq hne_nsq
      | Black =>
        have hK := h_black sq p h_sq hc
        have := h_legal.2 sq bk ⟨p, h_sq, hK, hc⟩ ⟨_, hbk, rfl, rfl⟩
        exact absurd this hne_bk
  -- Show kings not adjacent
  have h_not_adj : ¬ Movement.isKingStep wk bk := by
    intro h_step
    have h_adj : squaresAdjacent wk bk = true :=
      isKingStep_implies_squaresAdjacent wk bk h_step
    have ⟨_, h_kings_apart⟩ := h_legal
    have h_false := h_kings_apart wk bk ⟨_, hwk, rfl, rfl⟩ ⟨_, hbk, rfl, rfl⟩
    rw [h_false] at h_adj
    exact absurd h_adj (by decide)
  -- Construct KingsPlusMinor
  have hKPM : KingsPlusMinor gs.board wk bk nsq np := by
    refine ⟨?_, ?_, ?_, ?_, h_ne_wk_bk, h_nsq_ne_wk, h_nsq_ne_bk, ?_⟩
    · simpa using hwk
    · simpa using hbk
    · simpa using hnp
    · unfold isMinorPiece isMinorPieceType; right; exact hKnight
    · intro sq hne1 hne2 hne3
      simpa using h_empty sq hne1 hne2 hne3
  -- Construct KknInv
  have hInv : KknInv gs := ⟨wk, bk, nsq, np, hKPM, hKnight, h_not_adj⟩
  exact king_knight_vs_king_dead' gs hInv

/-- Endgame theorem: King + Bishop vs King cannot reach checkmate.
    A bishop only controls squares of one color (light or dark).
    The defending king can always escape to a square of the opposite color.

    **Justification**: A lone bishop cannot deliver checkmate because:
    1. Bishops move diagonally, staying on squares of one color
    2. A bishop on a light square can only ever attack light squares
    3. A bishop on a dark square can only ever attack dark squares
    4. The defending king always has adjacent squares of both colors available
    5. The attacking king cannot help trap because it must stay at distance >= 2
    6. Therefore, there's always an escape square of the opposite color

    This is a well-known chess endgame fact, verified by chess engine analysis.

    PROOF COMPLEXITY NOTE: A full formal proof requires:
    1. Proving bishops preserve their square color (bishop on light stays on light)
    2. Showing that every square has adjacent squares of the opposite color
    3. Demonstrating that the attacking king cannot simultaneously block all
       opposite-color escape squares while the bishop blocks same-color squares
    4. Induction on move sequences preserving the material configuration -/
-- Theorem 3: King + Bishop vs King is a dead position
-- Strategy: Bishop + King is insufficient mating material.
-- Uses the KMinorOrKkInv infrastructure which preserves the invariant through legal moves.
-- The core chess fact (K+B cannot checkmate) requires geometric analysis on square colors.

/-- K+B vs K is a dead position when we have the KkbInv invariant. -/
theorem king_bishop_vs_king_dead' (gs : GameState)
    (hInv : KkbInv gs) :
    isDeadPosition gs :=
  KkbOrKkInv.isDeadPosition gs (Or.inl hInv)

theorem king_bishop_vs_king_dead (gs : GameState)
    (h_white : whiteHasOnlyKingBishop gs)
    (h_black : blackHasOnlyKing gs)
    (h_legal : isLegalPosition gs.board)
    (h_wk : ∃ sq, gs.board sq = some (kingPiece Color.White))
    (h_bk : ∃ sq, gs.board sq = some (kingPiece Color.Black))
    (h_bishop : ∃ sq mp, gs.board sq = some mp ∧ mp.pieceType = PieceType.Bishop) :
    isDeadPosition gs := by
  -- Bridge to KkbInv
  obtain ⟨wk, hwk⟩ := h_wk
  obtain ⟨bk, hbk⟩ := h_bk
  obtain ⟨bsq, bp, hbp, hBishop⟩ := h_bishop
  -- Show wk ≠ bk
  have h_ne_wk_bk : wk ≠ bk := by
    intro heq; subst heq; rw [hwk] at hbk
    exact absurd hbk (by simp [kingPiece])
  -- Determine bishop color
  have h_bishop_white : bp.color = Color.White := by
    by_contra h_not_white
    have h_black_piece : bp.color = Color.Black := by
      cases bp.color <;> simp_all
    have h_king := h_black bsq bp hbp h_black_piece
    rw [h_king] at hBishop
    cases hBishop
  -- Show bsq ≠ wk and bsq ≠ bk
  have h_bsq_ne_wk : bsq ≠ wk := by
    intro heq; subst heq; rw [hbp] at hwk
    have : bp = kingPiece Color.White := Option.some.inj hwk
    rw [this] at hBishop; simp [kingPiece] at hBishop
  have h_bsq_ne_bk : bsq ≠ bk := by
    intro heq; subst heq; rw [hbp] at hbk
    have : bp = kingPiece Color.Black := Option.some.inj hbk
    rw [this] at hBishop; simp [kingPiece] at hBishop
  -- Show all other squares are empty
  have h_empty : ∀ sq, sq ≠ wk → sq ≠ bk → sq ≠ bsq → gs.board sq = none := by
    intro sq hne_wk hne_bk hne_bsq
    cases h_sq : gs.board sq with
    | none => rfl
    | some p =>
      cases hc : p.color with
      | White =>
        have htype := h_white sq p h_sq hc
        rcases htype with hK | hB
        · have := h_legal.1 sq wk ⟨p, h_sq, hK, hc⟩ ⟨_, hwk, rfl, rfl⟩
          exact absurd this hne_wk
        · -- Two white bishops are equal
          have h_eq : p = bp := by
            have hp_type : p.pieceType = PieceType.Bishop := hB
            have hp_color : p.color = Color.White := hc
            have hbp_type : bp.pieceType = PieceType.Bishop := hBishop
            have hbp_color : bp.color = Color.White := h_bishop_white
            cases p; cases bp
            simp only [Piece.mk.injEq] at *
            exact ⟨hp_type.trans hbp_type.symm, hp_color.trans hbp_color.symm⟩
          have h_sq_eq : sq = bsq := by
            rw [h_eq] at h_sq
            exact Option.some.inj (Eq.trans h_sq.symm hbp)
          exact absurd h_sq_eq hne_bsq
      | Black =>
        have hK := h_black sq p h_sq hc
        have := h_legal.2 sq bk ⟨p, h_sq, hK, hc⟩ ⟨_, hbk, rfl, rfl⟩
        exact absurd this hne_bk
  -- Show kings not adjacent
  have h_not_adj : ¬ Movement.isKingStep wk bk := by
    intro h_step
    have h_adj : squaresAdjacent wk bk = true :=
      isKingStep_implies_squaresAdjacent wk bk h_step
    have ⟨_, h_kings_apart⟩ := h_legal
    have h_false := h_kings_apart wk bk ⟨_, hwk, rfl, rfl⟩ ⟨_, hbk, rfl, rfl⟩
    rw [h_false] at h_adj
    exact absurd h_adj (by decide)
  -- Construct KingsPlusMinor
  have hKPM : KingsPlusMinor gs.board wk bk bsq bp := by
    refine ⟨?_, ?_, ?_, ?_, h_ne_wk_bk, h_bsq_ne_wk, h_bsq_ne_bk, ?_⟩
    · simpa using hwk
    · simpa using hbk
    · simpa using hbp
    · unfold isMinorPiece isMinorPieceType; left; exact hBishop
    · intro sq hne1 hne2 hne3
      simpa using h_empty sq hne1 hne2 hne3
  -- Construct KkbInv
  have hInv : KkbInv gs := ⟨wk, bk, bsq, bp, hKPM, hBishop, h_not_adj⟩
  exact king_bishop_vs_king_dead' gs hInv

-- Theorem 4: Bishops on same color squares is a dead position
-- Strategy: Same-color bishops collectively attack only one color of squares.
-- The defending king always has escape squares of the opposite color.
theorem same_color_bishops_dead (gs : GameState)
    (h : bishopsOnSameColorSquares gs) :
    isDeadPosition gs := by
  unfold isDeadPosition
  intro ⟨moves, gs', hOk, hMate⟩
  -- Same-color bishops cannot deliver checkmate because:
  -- - All bishop attacks cover only squares of one color
  -- - The defending king always has opposite-color escape squares
  -- - The attacking pieces cannot simultaneously block all escape squares
  -- This generalizes the single-bishop argument and requires
  -- showing the invariant is preserved through legal moves.
  sorry

/-- Theorem: The deadPosition heuristic correctly identifies dead positions.
    When deadPosition returns true, the position is formally dead.

    The proof connects the Boolean `deadPosition` function to the formal
    `isDeadPosition` property via the individual endgame theorems above.
    Each case where `deadPosition` returns true maps to a known chess endgame
    configuration where checkmate is impossible. -/
theorem deadPosition_sound_aux (gs : GameState) :
    deadPosition gs = true →
    isDeadPosition gs := by
  intro _h_dead
  -- The proof would unfold `deadPosition` and case split on material configurations,
  -- connecting each case to the appropriate insufficiency theorem:
  -- - K vs K: king_vs_king_dead (fully proved via KkInv)
  -- - K+N vs K: king_knight_vs_king_dead
  -- - K+B vs K: king_bishop_vs_king_dead
  -- - Same-color bishops: same_color_bishops_dead
  -- This requires ~200+ lines of case matching.
  sorry

-- Main soundness theorem: the deadPosition heuristic is sound
-- If deadPosition returns true, then the position is formally dead
theorem deadPosition_sound (gs : GameState) :
    deadPosition gs = true →
    isDeadPosition gs :=
  deadPosition_sound_aux gs

end Rules
end Chess
