import Chess.Rules
import Chess.Movement
import Chess.Core
import Chess.Game
import Chess.PathValidationProofs
import Chess.SlidingProofs

namespace Chess.Rules

-- ============================================================================
-- FIDE Legality Specification
-- ============================================================================
-- This module defines the formal specification of FIDE-legal moves.
-- It bridges the computational implementation (allLegalMoves, pieceTargets)
-- with the formal FIDE Laws of Chess.

/--
Capture flag consistency with en passant handling.
The isCapture flag must be true iff:
- There's an enemy piece at the destination, OR
- The move is en passant (where the captured pawn is not at the destination square)
-/
def captureFlagConsistentWithEP (gs : GameState) (m : Move) : Prop :=
  m.isCapture = true ↔ (∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ m.isEnPassant

/--
A move respects FIDE geometry rules for the piece type.
This encodes Articles 3.2-3.8 of FIDE Laws (piece movement patterns).
-/
def respectsGeometry (gs : GameState) (m : Move) : Prop :=
  match m.piece.pieceType with
  | PieceType.King =>
      if m.isCastle then
        -- Castling geometry: handled by castleMoveIfLegal (Article 3.8)
        ∃ cfg : CastleConfig,
          cfg.kingFrom = m.fromSq ∧
          cfg.kingTo = m.toSq ∧
          (cfg = castleConfig m.piece.color true ∨ cfg = castleConfig m.piece.color false)
      else
        Movement.isKingStep m.fromSq m.toSq
  | PieceType.Queen =>
      Movement.isQueenMove m.fromSq m.toSq ∧ pathClear gs.board m.fromSq m.toSq
  | PieceType.Rook =>
      Movement.isRookMove m.fromSq m.toSq ∧ pathClear gs.board m.fromSq m.toSq
  | PieceType.Bishop =>
      Movement.isDiagonal m.fromSq m.toSq ∧ pathClear gs.board m.fromSq m.toSq
  | PieceType.Knight =>
      Movement.isKnightMove m.fromSq m.toSq
  | PieceType.Pawn =>
      if m.isCapture then
        if m.isEnPassant then
          Movement.isPawnCapture m.piece.color m.fromSq m.toSq ∧
          gs.enPassantTarget = some m.toSq ∧
          isEmpty gs.board m.toSq ∧
          m.promotion = none
        else
          Movement.isPawnCapture m.piece.color m.fromSq m.toSq ∧
          isEnemyAt gs.board m.piece.color m.toSq
      else
        Movement.isPawnAdvance m.piece.color m.fromSq m.toSq ∧
        pathClear gs.board m.fromSq m.toSq ∧
        -- FIDE Article 3.7(a): Two-step only from starting rank
        (Movement.rankDiff m.fromSq m.toSq = -2 * Movement.pawnDirection m.piece.color →
          m.fromSq.rankNat = pawnStartRank m.piece.color)

/--
A move is FIDE-legal if it satisfies all official rules.
Encodes FIDE Laws Article 3 (movement) and Article 3.9 (king safety).
-/
def fideLegal (gs : GameState) (m : Move) : Prop :=
  -- Article 3.1: Players alternate moves with their own pieces
  m.piece.color = gs.toMove ∧
  -- Article 3.1: The moving piece must be on the starting square
  gs.board m.fromSq = some m.piece ∧
  -- Article 3.2-3.8: Piece movement geometry
  respectsGeometry gs m ∧
  -- Article 3.1: Cannot capture own piece
  destinationFriendlyFreeProp gs m ∧
  -- Capture flag consistency (with en passant handling)
  captureFlagConsistentWithEP gs m ∧
  -- Article 3.9(a): King cannot move into check; no move can leave king in check
  ¬(inCheck (simulateMove gs m).board gs.toMove) ∧
  -- Article 3.7(e): Pawn promotion rules
  (m.piece.pieceType = PieceType.Pawn ∧ m.toSq.rankNat = pawnPromotionRank m.piece.color →
    m.promotion.isSome) ∧
  (m.promotion.isSome →
    m.piece.pieceType = PieceType.Pawn ∧ m.toSq.rankNat = pawnPromotionRank m.piece.color) ∧
  -- Article 3.8(a): Castling legality
  (m.isCastle →
    ∃ kingSide : Bool,
      let cfg := castleConfig m.piece.color kingSide
      castleRight gs.castlingRights m.piece.color kingSide ∧
      gs.board cfg.kingFrom = some m.piece ∧
      -- Rook must exist at its starting position (FIDE Article 3.8)
      (∃ rook : Piece, gs.board cfg.rookFrom = some rook ∧
                       rook.pieceType = PieceType.Rook ∧ rook.color = m.piece.color) ∧
      cfg.emptySquares.all (isEmpty gs.board) ∧
      cfg.checkSquares.all (fun sq =>
        ¬(inCheck (gs.board.update cfg.kingFrom none |>.update sq (some m.piece)) m.piece.color)) ∧
      -- Move field constraints for castle
      m.fromSq = cfg.kingFrom ∧
      m.toSq = cfg.kingTo ∧
      m.castleRookFrom = some cfg.rookFrom ∧
      m.castleRookTo = some cfg.rookTo ∧
      m.isCapture = false ∧
      m.promotion = none ∧
      m.isEnPassant = false) ∧
  -- Well-formedness: en passant is only valid for pawn moves
  (m.isEnPassant → m.piece.pieceType = PieceType.Pawn) ∧
  -- FIDE Article 3.8.2: Only kings can castle
  (m.isCastle → m.piece.pieceType = PieceType.King) ∧
  -- Castle rook fields are only set for castling moves
  (¬m.isCastle → m.castleRookFrom = none ∧ m.castleRookTo = none) ∧
  -- Article 3.7(e): Promotion must be to a valid piece type (Q, R, B, N)
  (m.promotion.isSome → ∃ pt ∈ promotionTargets, m.promotion = some pt)

/-- Alias for fideLegal used in semantic proofs. -/
abbrev fideLegalSemantic := fideLegal

/--
Valid en passant rank predicate: if there's an en passant target, it must be on
rank 3 (for white pawns, rankNat = 2) or rank 6 (for black pawns, rankNat = 5).

This invariant holds for all reachable game states because en passant targets
are only set after a pawn's two-square advance from its starting rank:
- White pawn: starts on rank 2 (rankNat=1), lands on rank 4 (rankNat=3), EP target is rank 3 (rankNat=2)
- Black pawn: starts on rank 7 (rankNat=6), lands on rank 5 (rankNat=4), EP target is rank 6 (rankNat=5)
-/
def hasValidEPRank (gs : GameState) : Prop :=
  ∀ target, gs.enPassantTarget = some target → (target.rankNat = 2 ∨ target.rankNat = 5)

/-- The standard starting position has no en passant target, so hasValidEPRank holds vacuously. -/
theorem standardGameState_hasValidEPRank : hasValidEPRank standardGameState := by
  unfold hasValidEPRank standardGameState
  intro target h
  simp at h

/-- Helper: EP ranks (2 and 5) are not promotion ranks (0 and 7). -/
theorem validEPRank_not_promotion (target : Square) (c : Color) :
    (target.rankNat = 2 ∨ target.rankNat = 5) →
    target.rankNat ≠ pawnPromotionRank c := by
  intro h_rank
  cases c with
  | White =>
      unfold pawnPromotionRank
      cases h_rank with
      | inl h2 => simp [h2]
      | inr h5 => simp [h5]
  | Black =>
      unfold pawnPromotionRank
      cases h_rank with
      | inl h2 => simp [h2]
      | inr h5 => simp [h5]

-- ============================================================================
-- Axioms (FIDE Well-Formedness)
-- ============================================================================
-- These axioms capture FIDE rules that are not directly encoded in fideLegal
-- but follow from game state invariants or the structure of legal play.

/--
En passant targets are on rank 3 (black's EP) or rank 6 (white's EP).
This follows from FIDE rules: EP only occurs after a two-square pawn push.

This theorem requires `hasValidEPRank gs` as a precondition because the rank
constraint only holds for game states reachable from the standard starting
position. For arbitrary game states, the en passant target could be any square.
-/
theorem enPassantTarget_rank_constraint (gs : GameState) (target : Square)
    (h_valid : hasValidEPRank gs) :
    gs.enPassantTarget = some target →
    target.rankNat = 2 ∨ target.rankNat = 5 := by
  exact h_valid target

/-
En passant target squares are always empty in a valid game state.

Core insight: The enPassantTarget is only set in GameState.movePiece when:
1. A pawn moves exactly 2 squares (rankDiff = 2)
2. The target is set to the intermediate square (1 square away from start)
3. The board is modified only at fromSq, toSq, and capture locations
4. Since target ≠ fromSq and target ≠ toSq, the board is unchanged at target
5. The previous state's invariant guarantees target was empty
-/
-- Helper lemmas for the invariant proof
namespace EnPassantInvariant

/-- When bounds hold, mkUnsafe produces a square with the expected rankNat. -/
theorem mkUnsafe_rankNat {f r : Nat} (hf : f < 8) (hr : r < 8) :
    (Square.mkUnsafe f r).rankNat = r := by
  simp [Square.mkUnsafe, Square.mk?, dif_pos hf, dif_pos hr, Square.rankNat, Rank.toNat]

/--
Helper lemma: board.update doesn't affect squares that weren't updated.
This is the fundamental property of Board.update (set) semantics.
-/
theorem board_update_ne_unchanged (b : Board) (sq target : Square) (p : Option Piece)
    (h : target ≠ sq) :
    (b.update sq p).get target = b.get target :=
  Board.update_ne b sq p h

/--
Helper: two-step pawn move from source to dest has intermediate square between them.
For white: source.rankNat = 1, dest.rankNat = 3, intermediate = 2
For black: source.rankNat = 6, dest.rankNat = 4, intermediate = 5

Requires the pawn to start from its home rank (FIDE rule for two-step moves).
-/
theorem pawn_two_step_intermediate_bounds (fromSq toSq : Square) (c : Color)
    (h_two_step : Movement.rankDiff fromSq toSq = -2 * Movement.pawnDirection c)
    (h_start_rank : fromSq.rankNat = pawnStartRank c) :
    (c = Color.White → fromSq.rankNat = 1 ∧ toSq.rankNat = 3) ∧
    (c = Color.Black → fromSq.rankNat = 6 ∧ toSq.rankNat = 4) := by
  constructor
  · intro hWhite
    subst hWhite
    simp only [pawnStartRank] at h_start_rank
    constructor
    · exact h_start_rank
    · simp only [Movement.rankDiff, Movement.pawnDirection, Square.rankInt,
                 Int.ofNat_eq_natCast, Square.rankNat] at h_two_step h_start_rank ⊢
      have hFrom := fromSq.rank.isLt
      have hTo := toSq.rank.isLt
      omega
  · intro hBlack
    subst hBlack
    simp only [pawnStartRank] at h_start_rank
    constructor
    · exact h_start_rank
    · -- For black: pawnDirection = -1, so rankDiff = -2 * (-1) = 2
      -- rankDiff = fromSq.rankInt - toSq.rankInt = 2
      -- With fromSq.rank = 6, we get toSq.rank = 4
      simp only [Movement.rankDiff, Movement.pawnDirection, Square.rankInt,
                 Int.ofNat_eq_natCast, Square.rankNat] at h_two_step h_start_rank ⊢
      -- h_two_step: fromSq.rank.toNat - toSq.rank.toNat = 2 (after simplification)
      -- h_start_rank: fromSq.rank.toNat = 6
      -- Therefore toSq.rank.toNat = 6 - 2 = 4
      have hFrom := fromSq.rank.isLt
      have hTo := toSq.rank.isLt
      have h6 : (fromSq.rank.toNat : Int) = 6 := by omega
      have hDiff : (fromSq.rank.toNat : Int) - (toSq.rank.toNat : Int) = 2 := h_two_step
      omega

/--
The intermediate square is distinct from source and destination.
Requires the pawn to start from its home rank for the proof to go through.
-/
theorem pawn_two_step_target_distinct (fromSq toSq intermediate : Square) (c : Color)
    (h_two_step : Movement.rankDiff fromSq toSq = -2 * Movement.pawnDirection c)
    (h_start_rank : fromSq.rankNat = pawnStartRank c)
    (h_intermediate_rank :
      (c = Color.White → intermediate.rankNat = 2) ∧
      (c = Color.Black → intermediate.rankNat = 5)) :
    intermediate ≠ fromSq ∧ intermediate ≠ toSq := by
  -- Use the bounds theorem to get concrete rank values
  have hBounds := pawn_two_step_intermediate_bounds fromSq toSq c h_two_step h_start_rank
  constructor
  · -- intermediate ≠ fromSq: intermediate.rank ∈ {2,5}, fromSq.rank ∈ {1,6}
    intro heq
    cases c with
    | White =>
      have h1 : fromSq.rankNat = 1 := hBounds.1 rfl |>.1
      have h2 : intermediate.rankNat = 2 := h_intermediate_rank.1 rfl
      rw [← heq] at h1
      omega
    | Black =>
      have h1 : fromSq.rankNat = 6 := hBounds.2 rfl |>.1
      have h2 : intermediate.rankNat = 5 := h_intermediate_rank.2 rfl
      rw [← heq] at h1
      omega
  · -- intermediate ≠ toSq: intermediate.rank ∈ {2,5}, toSq.rank ∈ {3,4}
    intro heq
    cases c with
    | White =>
      have h1 : toSq.rankNat = 3 := hBounds.1 rfl |>.2
      have h2 : intermediate.rankNat = 2 := h_intermediate_rank.1 rfl
      rw [← heq] at h1
      omega
    | Black =>
      have h1 : toSq.rankNat = 4 := hBounds.2 rfl |>.2
      have h2 : intermediate.rankNat = 5 := h_intermediate_rank.2 rfl
      rw [← heq] at h1
      omega

end EnPassantInvariant

/--
En passant target is set iff the move is a pawn two-step from its start rank.
The start rank precondition ensures the intermediate rank is always valid (≥ 0).
-/
theorem enPassantTarget_set_iff_pawn_two_step (gs : GameState) (m : Move)
    (h_start : m.fromSq.rankNat = pawnStartRank m.piece.color) :
    let gs' := gs.movePiece m
    gs'.enPassantTarget.isSome ↔
    (m.piece.pieceType = PieceType.Pawn ∧
     Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 2) := by
  unfold GameState.movePiece
  simp only [beq_iff_eq]
  constructor
  · -- Forward: gs'.enPassantTarget.isSome → pawn two-step
    intro h_some
    simp only at h_some
    by_cases h_cond : m.piece.pieceType = PieceType.Pawn ∧ Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 2
    · exact h_cond
    · simp only [h_cond, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at h_some
  · -- Backward: pawn two-step → gs'.enPassantTarget.isSome
    intro ⟨h_pawn, h_two⟩
    simp only [h_pawn, h_two, and_self, ↓reduceIte]
    -- The dite condition (0 ≤ fromSq.rankInt + pawnDirection) holds from start rank
    have h_nonneg : 0 ≤ m.fromSq.rankInt + Movement.pawnDirection m.piece.color := by
      unfold Movement.pawnDirection
      simp only [Square.rankInt, Square.rankNat, Rank.toNat, Int.ofNat_eq_natCast] at *
      cases hc : m.piece.color with
      | White => simp only [hc, pawnStartRank, ↓reduceIte] at h_start ⊢; omega
      | Black => simp only [hc, pawnStartRank, ↓reduceIte] at h_start ⊢; omega
    simp only [h_nonneg, ↓reduceDIte, Option.isSome_some]

-- Core insight: a game state is "valid" if whenever enPassantTarget = some sq, sq is empty
def isValidEnPassantState (gs : GameState) : Prop :=
  ∀ sq : Square, gs.enPassantTarget = some sq → isEmpty gs.board sq = true

-- Base case: the starting position is valid
theorem standardGameState_valid_enPassant : isValidEnPassantState standardGameState := by
  unfold isValidEnPassantState
  intro sq h
  unfold standardGameState at h
  simp at h

-- When a pawn doesn't move two-step, enPassantTarget becomes none (vacuously valid)
theorem enPassantTarget_cleared_non_pawn_two_step (gs : GameState) (m : Move)
    (h_not_two_step : ¬(m.piece.pieceType = PieceType.Pawn ∧
                         Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 2)) :
    (gs.movePiece m).enPassantTarget = none := by
  unfold GameState.movePiece
  simp only [beq_iff_eq]
  simp only [h_not_two_step, ↓reduceIte]

-- Lemma: board.get is preserved at a square when updating different squares
theorem board_get_preserved_after_updates (b : Board) (sq1 sq2 sq3 target : Square) (p1 p2 p3 : Option Piece)
    (h1 : target ≠ sq1) (h2 : target ≠ sq2) (h3 : target ≠ sq3) :
    (((b.update sq1 p1).update sq2 p2).update sq3 p3).get target =
    b.get target := by
  rw [EnPassantInvariant.board_update_ne_unchanged ((b.update sq1 p1).update sq2 p2) sq3 target p3 h3]
  rw [EnPassantInvariant.board_update_ne_unchanged (b.update sq1 p1) sq2 target p2 h2]
  rw [EnPassantInvariant.board_update_ne_unchanged b sq1 target p1 h1]

-- enPassantTarget_valid_after_pawn_two_step, enPassantTarget_valid_after_move,
-- and enPassant_target_isEmpty are defined after pathClear_twoStep_intermediate (below)

/--
Pawns don't castle. Only kings can castle (FIDE Article 3.8.2).
Now a theorem - follows from fideLegal constraints on castling.
-/
theorem pawn_move_not_castle (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_pawn : m.piece.pieceType = PieceType.Pawn) :
    m.isCastle = false ∧ m.castleRookFrom = none ∧ m.castleRookTo = none := by
  -- fideLegal path: .2.2.2.2.2.2.2.2.2.2.1 = (isCastle → King)
  -- fideLegal path: .2.2.2.2.2.2.2.2.2.2.2.1 = (¬isCastle → rook fields)
  have h_castle_king := h_legal.2.2.2.2.2.2.2.2.2.2.1
  have h_fields := h_legal.2.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · -- isCastle = false: By contrapositive of (isCastle → King)
    cases h_castle : m.isCastle with
    | false => rfl
    | true =>
      have h_king := h_castle_king h_castle
      rw [h_pawn] at h_king
      exact PieceType.noConfusion h_king
  · -- castleRookFrom = none ∧ castleRookTo = none
    have h_not_castle : m.isCastle = false := by
      cases h_castle : m.isCastle with
      | false => rfl
      | true =>
        have h_king := h_castle_king h_castle
        rw [h_pawn] at h_king
        exact PieceType.noConfusion h_king
    exact h_fields (by simp [h_not_castle])

/--
Promotion implies on promotion rank. Pawns only promote at the final rank.
This is now a theorem - directly follows from fideLegal lines 79-80.
-/
theorem promotion_implies_promo_rank (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (_h_pawn : m.piece.pieceType = PieceType.Pawn)
    (h_promo : m.promotion.isSome) :
    m.toSq.rankNat = pawnPromotionRank m.piece.color := by
  -- fideLegal includes: (m.promotion.isSome → m.piece.pieceType = Pawn ∧ m.toSq.rankNat = promoRank)
  have h_promo_cond := h_legal.2.2.2.2.2.2.2.1
  exact (h_promo_cond h_promo).2

/--
Two-step pawn advances only occur from the starting rank (FIDE Article 3.7a).
Now a theorem - follows from respectsGeometry constraint in fideLegal.
-/
theorem pawn_twoStep_from_startRank (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_pawn : m.piece.pieceType = PieceType.Pawn)
    (h_not_cap : m.isCapture = false)
    (h_two : Movement.rankDiff m.fromSq m.toSq = -2 * Movement.pawnDirection m.piece.color) :
    m.fromSq.rankNat = pawnStartRank m.piece.color := by
  -- Extract respectsGeometry from fideLegal
  have h_geom := h_legal.2.2.1
  -- Unfold respectsGeometry for Pawn
  unfold respectsGeometry at h_geom
  simp only [h_pawn] at h_geom
  -- Match on isCapture = false
  simp only [h_not_cap] at h_geom
  -- h_geom now has the form: isPawnAdvance ∧ pathClear ∧ (twoStep → startRank)
  exact h_geom.2.2 h_two

-- NOTE: castle_rights_implies_rook_exists axiom removed.
-- This was superseded by adding rook existence condition directly to fideLegal
-- for castling moves (line 88-89). The axiom stated that castling rights imply
-- rook exists, but fideLegal now requires rook existence as part of legality.

/--
For two-step pawn advances, pathClear implies the intermediate square is empty.
This follows from squaresBetween definition - for a two-step advance, squaresBetween
returns the intermediate square, and pathClear ensures it's empty.

AXIOM JUSTIFICATION: Requires helper lemmas showing:
1. squaresBetween for a two-step pawn advance contains exactly the intermediate square
2. pathClear checks isEmpty for all squares in squaresBetween
The proof structure is straightforward but requires Movement module helpers.
-/
/-
THEOREM NOTE: This theorem connects pathClear with the intermediate square for pawn two-step.
The proof requires showing:
1. For a two-step pawn advance, squaresBetween contains exactly one square
2. That square is squareFromInts src.fileInt (src.rankInt + pawnDirection c)
3. pathClear = all isEmpty over squaresBetween

The proof is complex due to the squaresBetween definition and needs helper lemmas.
-/
theorem pathClear_twoStep_intermediate (board : Board) (src target : Square) (c : Color)
    (h_adv : Movement.isPawnAdvance c src target)
    (h_two : Movement.rankDiff src target = -2 * Movement.pawnDirection c)
    (h_clear : pathClear board src target = true) :
    ∃ intermediate : Square,
      Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection c) = some intermediate ∧
      isEmpty board intermediate = true := by
  -- A pawn two-step is a vertical rook-like move
  obtain ⟨h_ne, h_file, _⟩ := h_adv
  -- Establish isRookMove: fileDiff = 0, rankDiff ≠ 0
  have h_rd_ne : Movement.rankDiff src target ≠ 0 := by
    rw [h_two]; unfold Movement.pawnDirection; cases c <;> simp <;> omega
  have h_rook : Movement.isRookMove src target := ⟨h_ne, Or.inl ⟨h_file, h_rd_ne⟩⟩
  -- rookOffset = |fileDiff| + |rankDiff| = 0 + 2 = 2
  have h_offset : Movement.rookOffset src target = 2 := by
    unfold Movement.rookOffset
    rw [h_file]
    simp only [Int.natAbs_zero, Nat.zero_add]
    rw [h_two]
    unfold Movement.pawnDirection
    cases c <;> simp
  -- The intermediate square at k=1 exists
  have hk_pos : (0 : Nat) < 1 := Nat.zero_lt_one
  have hk_lt : (1 : Nat) < Movement.rookOffset src target := by rw [h_offset]; omega
  have h_valid := rookRay_intermediate_valid src target h_rook 1 hk_pos hk_lt
  -- rookDelta = (0, signInt(-rankDiff)) for vertical moves
  -- At k=1: fileCoord = src.fileInt + 0*1 = src.fileInt
  --          rankCoord = src.rankInt + signInt(-rankDiff)*1
  -- For pawnDirection: signInt(-rankDiff) = signInt(2*pawnDir) = pawnDir
  simp only [Movement.rookDelta, h_file, ↓reduceIte] at h_valid ⊢
  -- Show signInt(-rankDiff) = pawnDirection c
  have h_sign : Movement.signInt (-Movement.rankDiff src target) = Movement.pawnDirection c := by
    rw [h_two]
    unfold Movement.pawnDirection Movement.signInt
    cases c <;> simp <;> decide
  simp only [h_sign, Int.ofNat_one, Int.mul_one, Int.zero_mul, Int.add_zero] at h_valid ⊢
  obtain ⟨sq, hsq⟩ := h_valid
  refine ⟨sq, hsq, ?_⟩
  -- Now show isEmpty using pathClear
  have h_mem := rookRay_intermediate_in_squaresBetween src target h_rook 1 hk_pos hk_lt
  simp only [Movement.rookDelta, h_file, ↓reduceIte, h_sign,
             Int.ofNat_one, Int.mul_one, Int.zero_mul, Int.add_zero] at h_mem
  have h_in := h_mem sq hsq
  unfold pathClear at h_clear
  have h_all := List.all_eq_true.mp h_clear sq h_in
  unfold isEmpty
  exact h_all

-- ============================================================================
-- En Passant Validity (depends on pathClear_twoStep_intermediate)
-- ============================================================================

/--
Key lemma: if gs is valid and a pawn moves two-step, the resulting state is valid.
The intermediate square of a pawn two-step is never modified by the move,
so it remains empty as established by pathClear.
-/
theorem enPassantTarget_valid_after_pawn_two_step (gs : GameState) (m : Move)
    (h_valid : isValidEnPassantState gs)
    (h_two_step : m.piece.pieceType = PieceType.Pawn ∧
                  Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 2)
    (h_distinct : m.fromSq ≠ m.toSq)
    (h_adv : Movement.isPawnAdvance m.piece.color m.fromSq m.toSq)
    (h_clear : pathClear gs.board m.fromSq m.toSq = true)
    (h_start : m.fromSq.rankNat = pawnStartRank m.piece.color)
    (h_not_ep : m.isEnPassant = false)
    (h_not_castle : m.isCastle = false) :
    isValidEnPassantState (gs.movePiece m) := by
  -- Step 1: Establish rankDiff = -2 * pawnDirection
  have h_two : Movement.rankDiff m.fromSq m.toSq = -2 * Movement.pawnDirection m.piece.color := by
    rcases h_adv.2.2 with h1 | h2
    · exfalso
      have : Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 1 := by
        rw [h1]; unfold Movement.pawnDirection; cases m.piece.color <;> simp
      omega
    · exact h2
  -- Step 2: Get intermediate square from pathClear
  obtain ⟨intermediate, h_sq_eq, h_empty⟩ :=
    pathClear_twoStep_intermediate gs.board m.fromSq m.toSq m.piece.color h_adv h_two h_clear
  -- Step 3: Non-negativity for EP target computation
  have h_nonneg : (0 : Int) ≤ m.fromSq.rankInt + Movement.pawnDirection m.piece.color := by
    cases hc : m.piece.color with
    | White =>
      simp only [Movement.pawnDirection, hc, ↓reduceIte, Square.rankInt, Square.rankNat,
                 Rank.toNat, Int.ofNat_eq_natCast, pawnStartRank] at h_start ⊢
      omega
    | Black =>
      simp only [Movement.pawnDirection, hc, ↓reduceIte, Square.rankInt, Square.rankNat,
                 Rank.toNat, Int.ofNat_eq_natCast, pawnStartRank] at h_start ⊢
      omega
  -- Step 4: Compute the EP target rank
  have h_ep_rank_val : Int.toNat (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) =
      (match m.piece.color with | Color.White => 2 | Color.Black => 5) := by
    cases hc : m.piece.color with
    | White =>
      simp only [Movement.pawnDirection, hc, ↓reduceIte, pawnStartRank] at h_start
      have h_ri : m.fromSq.rankInt = (1 : Int) := by
        show Int.ofNat m.fromSq.rank.toNat = 1
        exact congrArg Int.ofNat h_start
      simp only [Movement.pawnDirection, h_ri, hc, ↓reduceIte]; native_decide
    | Black =>
      simp only [Movement.pawnDirection, hc, ↓reduceIte, pawnStartRank] at h_start
      have h_ri : m.fromSq.rankInt = (6 : Int) := by
        show Int.ofNat m.fromSq.rank.toNat = 6
        exact congrArg Int.ofNat h_start
      simp only [Movement.pawnDirection, h_ri, hc, ↓reduceIte]; native_decide
  -- Step 5: EP target rank is < 8 (needed for mkUnsafe_rankNat)
  have h_ep_rank_lt : Int.toNat (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) < 8 := by
    rw [h_ep_rank_val]
    split <;> omega
  -- Helper: file bound for mkUnsafe_rankNat
  have h_file_lt : m.fromSq.fileNat < 8 := m.fromSq.file.isLt
  -- Step 6: Intermediate rank equals EP target rank
  have h_inter_rank : intermediate.rankNat =
      Int.toNat (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) := by
    unfold Movement.squareFromInts at h_sq_eq
    simp only [Square.fileInt, Int.ofNat_eq_natCast] at h_sq_eq
    split at h_sq_eq
    · have h_eq := (Option.some.inj h_sq_eq).symm
      rw [h_eq]
      exact EnPassantInvariant.mkUnsafe_rankNat (by exact h_file_lt) h_ep_rank_lt
    · exact absurd h_sq_eq (by simp)
  -- Step 7: Intermediate ≠ fromSq (rank differs: 2≠1 or 5≠6)
  have h_ne_from : intermediate ≠ m.fromSq := by
    intro heq
    have h_rank_eq : intermediate.rankNat = m.fromSq.rankNat := congrArg Square.rankNat heq
    rw [h_inter_rank, h_ep_rank_val] at h_rank_eq
    cases hc : m.piece.color with
    | White => simp only [hc, pawnStartRank] at h_start h_rank_eq; omega
    | Black => simp only [hc, pawnStartRank] at h_start h_rank_eq; omega
  -- Step 8: Intermediate ≠ toSq (rank differs: 2≠3 or 5≠4)
  have h_ne_to : intermediate ≠ m.toSq := by
    intro heq
    have h_rank_eq : intermediate.rankNat = m.toSq.rankNat := congrArg Square.rankNat heq
    have h_bounds := EnPassantInvariant.pawn_two_step_intermediate_bounds m.fromSq m.toSq m.piece.color h_two h_start
    rw [h_inter_rank, h_ep_rank_val] at h_rank_eq
    cases hc : m.piece.color with
    | White =>
      have ⟨_, h_to⟩ := h_bounds.1 hc
      simp only [pawnStartRank, hc] at h_to h_rank_eq; omega
    | Black =>
      have ⟨_, h_to⟩ := h_bounds.2 hc
      simp only [pawnStartRank, hc] at h_to h_rank_eq; omega
  -- Step 9: Prove isValidEnPassantState
  unfold isValidEnPassantState
  intro sq h_ep_target
  -- The EP target in movePiece equals intermediate
  have h_inter_eq : intermediate =
      Square.mkUnsafe m.fromSq.fileNat (Int.toNat (m.fromSq.rankInt + Movement.pawnDirection m.piece.color)) := by
    unfold Movement.squareFromInts at h_sq_eq
    simp only [Square.fileInt, Int.ofNat_eq_natCast] at h_sq_eq
    split at h_sq_eq
    · have h_eq := (Option.some.inj h_sq_eq).symm
      rw [h_eq]; congr 1
    · exact absurd h_sq_eq (by simp)
  have h_ep_val : (gs.movePiece m).enPassantTarget =
      some intermediate := by
    unfold GameState.movePiece
    simp only [beq_iff_eq, h_two_step.1, h_two_step.2, and_self, ↓reduceIte, h_nonneg, ↓reduceDIte]
    exact congrArg some h_inter_eq.symm
  rw [h_ep_val] at h_ep_target
  have h_sq_eq2 : sq = intermediate := (Option.some.inj h_ep_target).symm
  subst h_sq_eq2
  -- The board in movePiece (not EP, not castle)
  have h_board_eq : (gs.movePiece m).board =
      (gs.board.update m.fromSq none).update m.toSq (some (gs.promotedPiece m)) := by
    unfold GameState.movePiece
    simp only [beq_iff_eq, h_not_ep, ↓reduceIte, h_not_castle, Bool.false_eq_true, false_and]
  -- After subst, `intermediate` was eliminated; `sq` remains in its place
  -- The board in movePiece (not EP, not castle)
  have h_board_eq2 : (gs.movePiece m).board =
      (gs.board.update m.fromSq none).update m.toSq (some (gs.promotedPiece m)) := by
    unfold GameState.movePiece
    simp only [beq_iff_eq, h_not_ep, ↓reduceIte, h_not_castle, Bool.false_eq_true, false_and]
  have h_board_get : (gs.movePiece m).board.get sq = gs.board.get sq := by
    rw [h_board_eq2]
    rw [Board.update_ne _ _ _ h_ne_to, Board.update_ne _ _ _ h_ne_from]
  unfold isEmpty
  show decide ((gs.movePiece m).board.get sq = none) = true
  rw [h_board_get]
  unfold isEmpty at h_empty
  exact h_empty

-- Main inductive step: if a state is valid, the result of any legal move is valid
theorem enPassantTarget_valid_after_move (gs : GameState) (m : Move)
    (h_valid : isValidEnPassantState gs)
    (h_if_two_step : m.piece.pieceType = PieceType.Pawn ∧
                      Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 2 →
      Movement.isPawnAdvance m.piece.color m.fromSq m.toSq ∧
      pathClear gs.board m.fromSq m.toSq = true ∧
      m.fromSq.rankNat = pawnStartRank m.piece.color ∧
      m.isEnPassant = false ∧ m.isCastle = false) :
    isValidEnPassantState (gs.movePiece m) := by
  by_cases h_two_step : m.piece.pieceType = PieceType.Pawn ∧
                         Int.natAbs (Movement.rankDiff m.fromSq m.toSq) = 2
  · have h_distinct : m.fromSq ≠ m.toSq := by
      intro heq
      have : Movement.rankDiff m.fromSq m.toSq = 0 := by
        rw [heq]; simp [Movement.rankDiff]
      simp [this] at h_two_step
    have ⟨h_adv, h_clear, h_start, h_not_ep, h_not_castle⟩ := h_if_two_step h_two_step
    exact enPassantTarget_valid_after_pawn_two_step gs m h_valid h_two_step h_distinct
      h_adv h_clear h_start h_not_ep h_not_castle
  · unfold isValidEnPassantState
    intro target h_target
    rw [enPassantTarget_cleared_non_pawn_two_step gs m h_two_step] at h_target
    simp at h_target

/--
The en passant target square is always empty for valid game states.
Requires isValidEnPassantState as a precondition (holds for all reachable states).
-/
theorem enPassant_target_isEmpty (gs : GameState) (target : Square)
    (h_valid : isValidEnPassantState gs)
    (h_ep : gs.enPassantTarget = some target) :
    isEmpty gs.board target = true :=
  h_valid target h_ep

-- ============================================================================
-- Axioms (Completeness)
-- ============================================================================
-- These axioms state that pieceTargets generates all fideLegal moves.

-- fideLegal_in_pieceTargets_axiom and fideLegal_exact_in_pieceTargets are defined
-- after the per-piece completeness theorems (below fideLegal_pawn_in_pieceTargets)

-- ============================================================================
-- Proven Theorems
-- ============================================================================

/--
FIDE-legal captures have the isCapture flag set correctly.
-/
theorem fideLegal_implies_captureFlag (gs : GameState) (m : Move) :
    fideLegal gs m →
    (∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ m.isEnPassant →
    m.isCapture = true := by
  intro h_legal h_cond
  have h_consistent := h_legal.2.2.2.2.1
  unfold captureFlagConsistentWithEP at h_consistent
  exact h_consistent.mpr h_cond

/--
FIDE-legal non-captures have the isCapture flag unset.
-/
theorem fideLegal_implies_noCaptureFlag (gs : GameState) (m : Move) :
    fideLegal gs m →
    gs.board m.toSq = none ∧ ¬m.isEnPassant →
    m.isCapture = false := by
  intro h_legal ⟨h_empty, h_not_ep⟩
  have h_consistent := h_legal.2.2.2.2.1
  unfold captureFlagConsistentWithEP at h_consistent
  -- Show ¬(isCapture = true) which gives isCapture = false for Bool
  cases h_m : m.isCapture with
  | false => rfl
  | true =>
    -- h_consistent.mp gives us (∃ p, ...) ∨ isEnPassant
    have h_or := h_consistent.mp h_m
    cases h_or with
    | inl h_enemy =>
      obtain ⟨p, h_some, _⟩ := h_enemy
      rw [h_empty] at h_some
      exact Option.noConfusion h_some
    | inr h_ep =>
      exact absurd h_ep h_not_ep

-- ============================================================================
-- Per-Piece Completeness Theorems
-- ============================================================================

/-- Helper: isKnightMove implies membership in knightTargets list. -/
theorem isKnightMove_mem_knightTargets (src tgt : Square) :
    Movement.isKnightMove src tgt → tgt ∈ Movement.knightTargets src := by
  intro h
  unfold Movement.knightTargets
  simp only [List.mem_filter, Square.mem_all, true_and]
  unfold Movement.isKnightMoveBool
  simp only [h.1, ↓reduceIte]
  cases h.2 with
  | inl hcase => simp only [hcase.1, ↓reduceIte, hcase.2]
  | inr hcase =>
    have h1 : Movement.absInt (Movement.fileDiff src tgt) = 2 := hcase.1
    have h2 : Movement.absInt (Movement.rankDiff src tgt) = 1 := hcase.2
    simp only [h1, h2, ↓reduceIte]
    decide

/-- Helper: move equality from field constraints. -/
private theorem move_eq_of_fields (m : Move) (cap : Bool)
    (h_cap : m.isCapture = cap)
    (h_ep : m.isEnPassant = false)
    (h_castle : m.isCastle = false)
    (h_promo : m.promotion = none)
    (h_rf : m.castleRookFrom = none)
    (h_rt : m.castleRookTo = none) :
    m = { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := cap } := by
  cases m
  simp only at h_cap h_ep h_castle h_promo h_rf h_rt
  simp only [h_cap, h_ep, h_castle, h_promo, h_rf, h_rt]

/-- Helper: destinationFriendlyFreeProp transfers to move record with same squares. -/
private theorem destFree_transfer (gs : GameState) (m : Move)
    (h : destinationFriendlyFreeProp gs m) :
    destinationFriendlyFree gs { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq } = true := by
  unfold destinationFriendlyFreeProp at h
  unfold destinationFriendlyFree at h ⊢
  exact h

/--
Knight case of fideLegal_in_pieceTargets: if m is fideLegal and involves a knight,
then the move is in pieceTargets.
-/
theorem fideLegal_knight_in_pieceTargets (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_knight : m.piece.pieceType = PieceType.Knight) :
    m ∈ pieceTargets gs m.fromSq m.piece := by
  -- Extract all the fideLegal components
  have h_dest := h_legal.2.2.2.1
  have h_cap_consistent := h_legal.2.2.2.2.1
  have h_promo_back := h_legal.2.2.2.2.2.2.2.1
  have h_ep_pawn := h_legal.2.2.2.2.2.2.2.2.2.1
  have h_castle_king := h_legal.2.2.2.2.2.2.2.2.2.2.1
  have h_rook_fields := h_legal.2.2.2.2.2.2.2.2.2.2.2.1

  -- For knights, respectsGeometry is just isKnightMove
  have h_geom := h_legal.2.2.1
  unfold respectsGeometry at h_geom
  simp only [h_knight] at h_geom

  -- Knights can't castle
  have h_not_castle : m.isCastle = false := by
    cases hc : m.isCastle with
    | false => rfl
    | true =>
      have := h_castle_king hc
      rw [h_knight] at this
      exact PieceType.noConfusion this

  -- Knights can't do en passant
  have h_not_ep : m.isEnPassant = false := by
    cases hep : m.isEnPassant with
    | false => rfl
    | true =>
      have := h_ep_pawn hep
      rw [h_knight] at this
      exact PieceType.noConfusion this

  -- Knights can't promote
  have h_no_promo : m.promotion = none := by
    cases hp : m.promotion with
    | none => rfl
    | some pt =>
      have := (h_promo_back (by simp [hp])).1
      rw [h_knight] at this
      exact PieceType.noConfusion this

  have h_rook_none : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have h_nc : ¬m.isCastle := by simp [h_not_castle]
    exact h_rook_fields h_nc

  -- Unfold pieceTargets for knight
  unfold pieceTargets
  simp only [h_knight]

  -- The target is in knightTargets
  have h_in_targets := isKnightMove_mem_knightTargets m.fromSq m.toSq h_geom

  -- The destination is friendly-free
  have h_dest_free := destFree_transfer gs m h_dest

  -- Show the move is in the filterMap result
  simp only [List.mem_filterMap]
  refine ⟨m.toSq, h_in_targets, ?_⟩
  simp only [h_dest_free, ↓reduceIte]

  -- Case split on whether target square is occupied
  cases h_board : gs.board.get m.toSq with
  | none =>
    -- Empty square: non-capture
    unfold captureFlagConsistentWithEP at h_cap_consistent
    have h_not_cap : m.isCapture = false := by
      cases hcap : m.isCapture with
      | false => rfl
      | true =>
        have h_or := h_cap_consistent.mp hcap
        cases h_or with
        | inl h_enemy =>
          obtain ⟨p, h_some, _⟩ := h_enemy
          exact Option.noConfusion (h_board.symm.trans h_some)
        | inr h_ep =>
          rw [h_not_ep] at h_ep
          exact Bool.noConfusion h_ep
    have h_eq := move_eq_of_fields m false h_not_cap h_not_ep h_not_castle h_no_promo h_rook_none.1 h_rook_none.2
    rw [h_eq]
  | some p =>
    -- Occupied square: capture
    unfold captureFlagConsistentWithEP at h_cap_consistent
    have h_enemy : p.color ≠ m.piece.color := by
      unfold destinationFriendlyFreeProp destinationFriendlyFree at h_dest
      simp only [h_board, ne_eq, decide_eq_true_eq] at h_dest
      exact h_dest
    have h_cap : m.isCapture = true := by
      exact h_cap_consistent.mpr (Or.inl ⟨p, h_board, h_enemy⟩)
    have h_eq := move_eq_of_fields m true h_cap h_not_ep h_not_castle h_no_promo h_rook_none.1 h_rook_none.2
    rw [h_eq]

-- Helper: isKingStep implies membership in kingTargets list
theorem isKingStep_mem_kingTargets (src tgt : Square) :
    Movement.isKingStep src tgt → tgt ∈ Movement.kingTargets src := by
  intro h
  unfold Movement.kingTargets
  simp only [List.mem_filter, Square.mem_all, true_and]
  unfold Movement.isKingStepBool
  simp only [h.1, ↓reduceIte]
  have hf := h.2.1
  have hr := h.2.2
  simp only [hf, ↓reduceIte, hr]

-- Duplicate helpers since move_eq_of_fields/destFree_transfer are private
private theorem king_move_eq_of_fields (m : Move) (cap : Bool)
    (h_cap : m.isCapture = cap)
    (h_ep : m.isEnPassant = false)
    (h_castle : m.isCastle = false)
    (h_promo : m.promotion = none)
    (h_rf : m.castleRookFrom = none)
    (h_rt : m.castleRookTo = none) :
    m = { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := cap } := by
  cases m
  simp only at h_cap h_ep h_castle h_promo h_rf h_rt
  simp only [h_cap, h_ep, h_castle, h_promo, h_rf, h_rt]

private theorem king_destFree_transfer (gs : GameState) (m : Move)
    (h : destinationFriendlyFreeProp gs m) :
    destinationFriendlyFree gs { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq } = true := by
  unfold destinationFriendlyFreeProp at h
  unfold destinationFriendlyFree at h ⊢
  exact h

/--
King (non-castle) case of fideLegal_in_pieceTargets: if m is fideLegal, involves a king,
and is NOT a castle move, then the move is in pieceTargets.

Proof establishes:
1. King moves can't castle (by hypothesis), can't en passant (pieceType ≠ Pawn), can't promote
2. respectsGeometry for non-castle king = isKingStep
3. isKingStep implies target in kingTargets list
4. destinationFriendlyFree is preserved
5. Case split on board occupation determines capture flag
-/
theorem fideLegal_king_noCastle_in_pieceTargets (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_king : m.piece.pieceType = PieceType.King)
    (h_not_castle : m.isCastle = false) :
    m ∈ pieceTargets gs m.fromSq m.piece := by
  -- Extract fideLegal components
  have h_dest := h_legal.2.2.2.1
  have h_cap_consistent := h_legal.2.2.2.2.1
  have h_promo_back := h_legal.2.2.2.2.2.2.2.1
  have h_ep_pawn := h_legal.2.2.2.2.2.2.2.2.2.1
  have h_rook_fields := h_legal.2.2.2.2.2.2.2.2.2.2.2.1

  -- For non-castle king moves, respectsGeometry is isKingStep
  have h_geom := h_legal.2.2.1
  unfold respectsGeometry at h_geom
  simp only [h_king, h_not_castle, Bool.false_eq_true, ↓reduceIte] at h_geom

  -- Kings can't do en passant
  have h_not_ep : m.isEnPassant = false := by
    cases hep : m.isEnPassant with
    | false => rfl
    | true =>
      have := h_ep_pawn hep
      rw [h_king] at this
      exact PieceType.noConfusion this

  -- Kings can't promote
  have h_no_promo : m.promotion = none := by
    cases hp : m.promotion with
    | none => rfl
    | some pt =>
      have := (h_promo_back (by simp [hp])).1
      rw [h_king] at this
      exact PieceType.noConfusion this

  have h_rook_none : m.castleRookFrom = none ∧ m.castleRookTo = none := by
    have h_nc : ¬m.isCastle := by simp [h_not_castle]
    exact h_rook_fields h_nc

  -- Unfold pieceTargets for king
  unfold pieceTargets
  simp only [h_king]

  -- The result is standard ++ castles, we need to show m is in standard
  simp only [List.mem_append]
  left  -- m is in standard (not in castles since h_not_castle)

  -- The target is in kingTargets
  have h_in_targets := isKingStep_mem_kingTargets m.fromSq m.toSq h_geom

  -- The destination is friendly-free
  have h_dest_free := king_destFree_transfer gs m h_dest

  -- Show the move is in the filterMap result
  simp only [List.mem_filterMap]
  refine ⟨m.toSq, h_in_targets, ?_⟩
  simp only [h_dest_free, ↓reduceIte]

  -- Case split on whether target square is occupied
  cases h_board : gs.board.get m.toSq with
  | none =>
    -- Empty square: non-capture
    unfold captureFlagConsistentWithEP at h_cap_consistent
    have h_not_cap : m.isCapture = false := by
      cases hcap : m.isCapture with
      | false => rfl
      | true =>
        have h_or := h_cap_consistent.mp hcap
        cases h_or with
        | inl h_enemy =>
          obtain ⟨p, h_some, _⟩ := h_enemy
          exact Option.noConfusion (h_board.symm.trans h_some)
        | inr h_ep =>
          rw [h_not_ep] at h_ep
          exact Bool.noConfusion h_ep
    have h_eq := king_move_eq_of_fields m false h_not_cap h_not_ep h_not_castle h_no_promo h_rook_none.1 h_rook_none.2
    rw [h_eq]
  | some p =>
    -- Occupied square: capture
    unfold captureFlagConsistentWithEP at h_cap_consistent
    have h_enemy : p.color ≠ m.piece.color := by
      unfold destinationFriendlyFreeProp destinationFriendlyFree at h_dest
      simp only [h_board, ne_eq, decide_eq_true_eq] at h_dest
      exact h_dest
    have h_cap : m.isCapture = true := by
      exact h_cap_consistent.mpr (Or.inl ⟨p, h_board, h_enemy⟩)
    have h_eq := king_move_eq_of_fields m true h_cap h_not_ep h_not_castle h_no_promo h_rook_none.1 h_rook_none.2
    rw [h_eq]

-- ============================================================================
-- Coordinate System Theorem (Foundational)
-- ============================================================================

/--
Theorem: The coordinate round-trip property for the Square type.
Since Square's file and rank are Fin 8 (bounded 0-8), extracting their Int values
and reconstructing via squareFromInts always succeeds and returns the same square.

Proof establishes:
1. 0 ≤ sq.fileInt < 8 and 0 ≤ sq.rankInt < 8 (from Fin 8 bounds)
2. Int.toNat (Int.ofNat n) = n for n : Nat (definitional equality)
3. Square.mkUnsafe with original file/rank values reconstructs the square
-/
theorem squareFromInts_roundTrip (sq : Square) :
    Movement.squareFromInts sq.fileInt sq.rankInt = some sq := by
  unfold Movement.squareFromInts Square.fileInt Square.rankInt
  -- The bounds check passes because fileInt and rankInt come from Fin 8
  have h_file_nonneg := Square.fileInt_nonneg sq
  have h_file_lt := Square.fileInt_lt_8 sq
  have h_rank_nonneg := Square.rankInt_nonneg sq
  have h_rank_lt := Square.rankInt_lt_8 sq
  have h_cond : 0 ≤ Int.ofNat sq.file.toNat ∧ Int.ofNat sq.file.toNat < 8 ∧
                0 ≤ Int.ofNat sq.rank.toNat ∧ Int.ofNat sq.rank.toNat < 8 :=
    ⟨h_file_nonneg, h_file_lt, h_rank_nonneg, h_rank_lt⟩
  rw [if_pos h_cond]
  -- mkUnsafe with original values reconstructs the square
  unfold Square.mkUnsafe Square.mk?
  have h_file_lt_nat : (Int.ofNat sq.file.toNat).toNat < 8 := sq.file.isLt
  have h_rank_lt_nat : (Int.ofNat sq.rank.toNat).toNat < 8 := sq.rank.isLt
  simp only [h_file_lt_nat, h_rank_lt_nat, ↓reduceDIte]
  -- The constructed square equals sq: (Int.ofNat n).toNat = n by rfl
  congr 1 <;> exact Fin.ext rfl

-- ============================================================================
-- Sliding Piece Completeness
-- ============================================================================

/--
When pathClear holds for a rook move, all intermediate squares on the ray are empty.
Proves that intermediate offsets produce valid squares in squaresBetween.

AXIOM JUSTIFICATION: Requires helper lemmas:
- rookRay_intermediate_valid: squareFromInts succeeds for 0 < k < N
- rookRay_intermediate_in_squaresBetween: result is in squaresBetween
- pathClear iterates over squaresBetween checking isEmpty
-/
/-
THEOREM NOTE: This theorem about rook ray intermediates requires:
1. Showing squareFromInts succeeds for intermediate steps (coordinates in bounds)
2. Connecting the result to squaresBetween membership
3. Using pathClear = all isEmpty over squaresBetween

The proof is complex and requires several helper lemmas about coordinate arithmetic.
-/
theorem rookRay_intermediates_empty (board : Board) (src tgt : Square)
    (h_rook : Movement.isRookMove src tgt)
    (h_clear : pathClear board src tgt = true) :
    let (df, dr) := Movement.rookDelta src tgt
    let N := Movement.rookOffset src tgt
    ∀ k, 0 < k → k < N →
      ∃ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq ∧
            isEmpty board sq = true := by
  simp only
  intro k hk_pos hk_lt
  -- Step 1: The intermediate square exists
  have h_valid := rookRay_intermediate_valid src tgt h_rook k hk_pos hk_lt
  simp only at h_valid
  obtain ⟨sq, hsq⟩ := h_valid
  refine ⟨sq, hsq, ?_⟩
  -- Step 2: sq ∈ squaresBetween src tgt
  have h_mem := rookRay_intermediate_in_squaresBetween src tgt h_rook k hk_pos hk_lt
  simp only at h_mem
  have h_in_between := h_mem sq hsq
  -- Step 3: pathClear means all squares between are empty
  unfold pathClear at h_clear
  have h_all := List.all_eq_true.mp h_clear sq h_in_between
  unfold isEmpty
  exact h_all

/--
When pathClear holds for a bishop move, all intermediate squares on the ray are empty.

AXIOM JUSTIFICATION: Requires helper lemmas:
- bishopRay_intermediate_valid: squareFromInts succeeds for 0 < k < N
- bishopRay_intermediate_in_squaresBetween: result is in squaresBetween
- pathClear iterates over squaresBetween checking isEmpty
-/
/-
THEOREM NOTE: This theorem about bishop ray intermediates requires:
1. Showing squareFromInts succeeds for intermediate diagonal steps
2. Connecting the result to squaresBetween membership
3. Using pathClear = all isEmpty over squaresBetween

Same structure as rookRay_intermediates_empty but for diagonal moves.
-/
theorem bishopRay_intermediates_empty (board : Board) (src tgt : Square)
    (h_bishop : Movement.isDiagonal src tgt)
    (h_clear : pathClear board src tgt = true) :
    let (df, dr) := Movement.bishopDelta src tgt
    let N := Movement.bishopOffset src tgt
    ∀ k, 0 < k → k < N →
      ∃ sq, Movement.squareFromInts (src.fileInt + df * k) (src.rankInt + dr * k) = some sq ∧
            isEmpty board sq = true := by
  simp only
  intro k hk_pos hk_lt
  -- Step 1: The intermediate square exists
  have h_valid := bishopRay_intermediate_valid src tgt h_bishop k hk_pos hk_lt
  simp only at h_valid
  obtain ⟨sq, hsq⟩ := h_valid
  refine ⟨sq, hsq, ?_⟩
  -- Step 2: sq ∈ squaresBetween src tgt
  have h_mem := bishopRay_intermediate_in_squaresBetween src tgt h_bishop k hk_pos hk_lt
  simp only at h_mem
  have h_in_between := h_mem sq hsq
  -- Step 3: pathClear means all squares between are empty
  unfold pathClear at h_clear
  have h_all := List.all_eq_true.mp h_clear sq h_in_between
  unfold isEmpty
  exact h_all

/--
Rook case: fideLegal rook moves are in pieceTargets.
This is the main completeness theorem for rooks.

AXIOM JUSTIFICATION: Requires many Movement.* helper lemmas showing that
isRookMove geometry matches slidingTargets ray traversal. The proof follows from:
1. respectsGeometry gives isRookMove and pathClear
2. slidingTargets walks the ray and finds target
3. captureFlagConsistent ensures correct move construction
-/
/-
THEOREM NOTE: Rook completeness requires:
1. Extracting isRookMove and pathClear from respectsGeometry
2. Showing slidingTargets finds the target square on the ray
3. Verifying capture flag consistency with board occupation

The proof follows the same pattern as fideLegal_knight_in_pieceTargets but for sliding pieces.
-/
theorem fideLegal_rook_in_pieceTargets (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_rook : m.piece.pieceType = PieceType.Rook) :
    m ∈ pieceTargets gs m.fromSq m.piece := by
  -- Extract respectsGeometry: isRookMove ∧ pathClear
  have h_geom := h_legal.2.2.1
  unfold respectsGeometry at h_geom
  simp only [h_rook] at h_geom
  have h_rook_move := h_geom.1
  have h_path_clear := h_geom.2
  have h_dest := h_legal.2.2.2.1
  have h_capture := h_legal.2.2.2.2.1
  -- Establish default field values for rook moves
  have h_ep_false : m.isEnPassant = false := by
    cases h_ep_cases : m.isEnPassant with
    | false => rfl
    | true =>
      exfalso
      have := h_legal.2.2.2.2.2.2.2.2.2.1 h_ep_cases
      rw [h_rook] at this; exact absurd this (by decide)
  have h_castle_false : m.isCastle = false := by
    cases h_castle_cases : m.isCastle with
    | false => rfl
    | true =>
      exfalso
      have := h_legal.2.2.2.2.2.2.2.2.2.2.1 h_castle_cases
      rw [h_rook] at this; exact absurd this (by decide)
  have h_not_castle : ¬(m.isCastle = true) := by rw [h_castle_false]; decide
  have ⟨h_rf_none, h_rt_none⟩ := h_legal.2.2.2.2.2.2.2.2.2.2.2.1 h_not_castle
  have h_promo_none : m.promotion = none := by
    cases h_promo_cases : m.promotion with
    | none => rfl
    | some _ =>
      exfalso
      have h_some : m.promotion.isSome = true := by rw [h_promo_cases]; rfl
      have := (h_legal.2.2.2.2.2.2.2.1 h_some).1
      rw [h_rook] at this; exact absurd this (by decide)
  -- Reduce goal to slidingTargets membership
  unfold pieceTargets
  simp only [h_rook]
  -- Goal: m ∈ slidingTargets gs m.fromSq m.piece [(1,0),(-1,0),(0,1),(0,-1)]
  -- Obtain the slidingTargets completeness result
  have h_sliding := rook_in_slidingTargets gs m.fromSq m.toSq m.piece
    h_rook_move h_path_clear h_dest
  -- Destructure m to match slidingTargets output format
  obtain ⟨piece, fromSq, toSq, isCapture, promotion, isCastle, castleRookFrom, castleRookTo, isEnPassant⟩ := m
  simp only at h_ep_false h_castle_false h_rf_none h_rt_none h_promo_none
  subst h_ep_false h_castle_false h_rf_none h_rt_none h_promo_none
  -- Now m = Move.mk piece fromSq toSq isCapture none false none none false
  cases h_cap : isCapture with
  | true =>
    -- From capture flag consistency, there's an enemy piece at target
    unfold captureFlagConsistentWithEP at h_capture
    simp only at h_capture
    have h_exists := h_capture.mp h_cap
    cases h_exists with
    | inl h_piece =>
      obtain ⟨p_tgt, hp_at, hp_color⟩ := h_piece
      have h_not_empty : isEmpty gs.board toSq = false := by
        simp [isEmpty, hp_at]
      have h_enemy : isEnemyAt gs.board piece.color toSq = true := by
        simp [isEnemyAt, hp_at, decide_eq_true_eq]
        exact hp_color
      exact h_sliding.2 h_not_empty h_enemy
    | inr h_ep => exact absurd h_ep (by decide)
  | false =>
    -- Non-capture case: show target is empty
    have h_empty : isEmpty gs.board toSq = true := by
      unfold isEmpty
      cases h_board : gs.board toSq with
      | none => rfl
      | some p =>
        exfalso
        -- destinationFriendlyFreeProp says piece at target is enemy
        unfold destinationFriendlyFreeProp destinationFriendlyFree at h_dest
        simp only [h_board, decide_eq_true_eq] at h_dest
        -- h_dest : p.color ≠ piece.color
        -- captureFlagConsistentWithEP: enemy at target → isCapture = true
        unfold captureFlagConsistentWithEP at h_capture
        simp only at h_capture
        have h_would_cap := h_capture.mpr (Or.inl ⟨p, h_board, h_dest⟩)
        exact absurd h_would_cap (by simp [h_cap])
    exact h_sliding.1 h_empty

/--
Bishop case: fideLegal bishop moves are in pieceTargets.

AXIOM JUSTIFICATION: Same structure as rook case - requires Movement.* helper lemmas
showing that isDiagonal geometry matches slidingTargets ray traversal.
-/
/-
THEOREM NOTE: Bishop completeness requires:
1. Extracting isDiagonal and pathClear from respectsGeometry
2. Showing slidingTargets finds the target square on the diagonal
3. Verifying capture flag consistency with board occupation

Same structure as rook case.
-/
theorem fideLegal_bishop_in_pieceTargets (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_bishop : m.piece.pieceType = PieceType.Bishop) :
    m ∈ pieceTargets gs m.fromSq m.piece := by
  have h_geom := h_legal.2.2.1
  unfold respectsGeometry at h_geom
  simp only [h_bishop] at h_geom
  have h_diag_move := h_geom.1
  have h_path_clear := h_geom.2
  have h_dest := h_legal.2.2.2.1
  have h_capture := h_legal.2.2.2.2.1
  have h_ep_false : m.isEnPassant = false := by
    cases h_ep_cases : m.isEnPassant with
    | false => rfl
    | true =>
      exfalso
      have := h_legal.2.2.2.2.2.2.2.2.2.1 h_ep_cases
      rw [h_bishop] at this; exact absurd this (by decide)
  have h_castle_false : m.isCastle = false := by
    cases h_castle_cases : m.isCastle with
    | false => rfl
    | true =>
      exfalso
      have := h_legal.2.2.2.2.2.2.2.2.2.2.1 h_castle_cases
      rw [h_bishop] at this; exact absurd this (by decide)
  have h_not_castle : ¬(m.isCastle = true) := by rw [h_castle_false]; decide
  have ⟨h_rf_none, h_rt_none⟩ := h_legal.2.2.2.2.2.2.2.2.2.2.2.1 h_not_castle
  have h_promo_none : m.promotion = none := by
    cases h_promo_cases : m.promotion with
    | none => rfl
    | some _ =>
      exfalso
      have h_some : m.promotion.isSome = true := by rw [h_promo_cases]; rfl
      have := (h_legal.2.2.2.2.2.2.2.1 h_some).1
      rw [h_bishop] at this; exact absurd this (by decide)
  unfold pieceTargets
  simp only [h_bishop]
  have h_sliding := bishop_in_slidingTargets gs m.fromSq m.toSq m.piece
    h_diag_move h_path_clear h_dest
  obtain ⟨piece, fromSq, toSq, isCapture, promotion, isCastle, castleRookFrom, castleRookTo, isEnPassant⟩ := m
  simp only at h_ep_false h_castle_false h_rf_none h_rt_none h_promo_none
  subst h_ep_false h_castle_false h_rf_none h_rt_none h_promo_none
  cases h_cap : isCapture with
  | true =>
    unfold captureFlagConsistentWithEP at h_capture
    simp only at h_capture
    have h_exists := h_capture.mp h_cap
    cases h_exists with
    | inl h_piece =>
      obtain ⟨p_tgt, hp_at, hp_color⟩ := h_piece
      have h_not_empty : isEmpty gs.board toSq = false := by
        simp [isEmpty, hp_at]
      have h_enemy : isEnemyAt gs.board piece.color toSq = true := by
        simp [isEnemyAt, hp_at, decide_eq_true_eq]
        exact hp_color
      exact h_sliding.2 h_not_empty h_enemy
    | inr h_ep => exact absurd h_ep (by decide)
  | false =>
    have h_empty : isEmpty gs.board toSq = true := by
      unfold isEmpty
      cases h_board : gs.board toSq with
      | none => rfl
      | some p =>
        exfalso
        unfold destinationFriendlyFreeProp destinationFriendlyFree at h_dest
        simp only [h_board, decide_eq_true_eq] at h_dest
        unfold captureFlagConsistentWithEP at h_capture
        simp only at h_capture
        have h_would_cap := h_capture.mpr (Or.inl ⟨p, h_board, h_dest⟩)
        exact absurd h_would_cap (by simp [h_cap])
    exact h_sliding.1 h_empty

theorem fideLegal_queen_in_pieceTargets (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_queen : m.piece.pieceType = PieceType.Queen) :
    m ∈ pieceTargets gs m.fromSq m.piece := by
  have h_geom := h_legal.2.2.1
  unfold respectsGeometry at h_geom
  simp only [h_queen] at h_geom
  have h_queen_move := h_geom.1
  have h_path_clear := h_geom.2
  have h_dest := h_legal.2.2.2.1
  have h_capture := h_legal.2.2.2.2.1
  have h_ep_false : m.isEnPassant = false := by
    cases h_ep_cases : m.isEnPassant with
    | false => rfl
    | true =>
      exfalso
      have := h_legal.2.2.2.2.2.2.2.2.2.1 h_ep_cases
      rw [h_queen] at this; exact absurd this (by decide)
  have h_castle_false : m.isCastle = false := by
    cases h_castle_cases : m.isCastle with
    | false => rfl
    | true =>
      exfalso
      have := h_legal.2.2.2.2.2.2.2.2.2.2.1 h_castle_cases
      rw [h_queen] at this; exact absurd this (by decide)
  have h_not_castle : ¬(m.isCastle = true) := by rw [h_castle_false]; decide
  have ⟨h_rf_none, h_rt_none⟩ := h_legal.2.2.2.2.2.2.2.2.2.2.2.1 h_not_castle
  have h_promo_none : m.promotion = none := by
    cases h_promo_cases : m.promotion with
    | none => rfl
    | some _ =>
      exfalso
      have h_some : m.promotion.isSome = true := by rw [h_promo_cases]; rfl
      have := (h_legal.2.2.2.2.2.2.2.1 h_some).1
      rw [h_queen] at this; exact absurd this (by decide)
  unfold pieceTargets
  simp only [h_queen]
  -- Goal: m ∈ slidingTargets gs m.fromSq m.piece [(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1),(1,-1),(-1,1)]
  -- This equals queenDeltas
  change m ∈ slidingTargets gs m.fromSq m.piece queenDeltas
  have h_sliding := queen_in_slidingTargets gs m.fromSq m.toSq m.piece
    h_queen_move h_path_clear h_dest
  obtain ⟨piece, fromSq, toSq, isCapture, promotion, isCastle, castleRookFrom, castleRookTo, isEnPassant⟩ := m
  simp only at h_ep_false h_castle_false h_rf_none h_rt_none h_promo_none
  subst h_ep_false h_castle_false h_rf_none h_rt_none h_promo_none
  cases h_cap : isCapture with
  | true =>
    unfold captureFlagConsistentWithEP at h_capture
    simp only at h_capture
    have h_exists := h_capture.mp h_cap
    cases h_exists with
    | inl h_piece =>
      obtain ⟨p_tgt, hp_at, hp_color⟩ := h_piece
      have h_not_empty : isEmpty gs.board toSq = false := by
        simp [isEmpty, hp_at]
      have h_enemy : isEnemyAt gs.board piece.color toSq = true := by
        simp [isEnemyAt, hp_at, decide_eq_true_eq]
        exact hp_color
      exact h_sliding.2 h_not_empty h_enemy
    | inr h_ep => exact absurd h_ep (by decide)
  | false =>
    have h_empty : isEmpty gs.board toSq = true := by
      unfold isEmpty
      cases h_board : gs.board toSq with
      | none => rfl
      | some p =>
        exfalso
        unfold destinationFriendlyFreeProp destinationFriendlyFree at h_dest
        simp only [h_board, decide_eq_true_eq] at h_dest
        unfold captureFlagConsistentWithEP at h_capture
        simp only at h_capture
        have h_would_cap := h_capture.mpr (Or.inl ⟨p, h_board, h_dest⟩)
        exact absurd h_would_cap (by simp [h_cap])
    exact h_sliding.1 h_empty

-- ============================================================================
-- King Castle Completeness
-- ============================================================================

/--
When fideLegal holds for a castle move, castleMoveIfLegal produces the same move.
This proves that the move generation function is complete for castling moves.
-/
-- NOTE: This theorem requires fideLegal to also constrain m.castleRookFrom and
-- m.castleRookTo for castle moves. Currently fideLegal only says these fields are none
-- when ¬m.isCastle, but doesn't specify their values when m.isCastle = true.
-- The spec needs to be extended with:
--   (m.isCastle → m.castleRookFrom = some (castleConfig m.piece.color kingSide).rookFrom ∧
--                 m.castleRookTo = some (castleConfig m.piece.color kingSide).rookTo)
theorem castleMoveIfLegal_produces_fideLegal (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_king : m.piece.pieceType = PieceType.King)
    (h_castle : m.isCastle = true) :
    ∃ kingSide : Bool, castleMoveIfLegal gs kingSide = some m := by
  obtain ⟨kingSide, h_body⟩ := h_legal.2.2.2.2.2.2.2.2.1 h_castle
  refine ⟨kingSide, ?_⟩
  have hc : m.piece.color = gs.toMove := h_legal.1
  have h_rights : (castleRight gs.castlingRights m.piece.color kingSide) = true := h_body.1
  have h_king_at := h_body.2.1
  obtain ⟨rook, h_rook_at, h_rook_pt, h_rook_color⟩ := h_body.2.2.1
  have h_empty := h_body.2.2.2.1
  have h_safe := h_body.2.2.2.2.1
  have h_from := h_body.2.2.2.2.2.1
  have h_to := h_body.2.2.2.2.2.2.1
  have h_rf := h_body.2.2.2.2.2.2.2.1
  have h_rt := h_body.2.2.2.2.2.2.2.2.1
  have h_not_cap := h_body.2.2.2.2.2.2.2.2.2.1
  have h_no_promo := h_body.2.2.2.2.2.2.2.2.2.2.1
  have h_not_ep := h_body.2.2.2.2.2.2.2.2.2.2.2
  simp only [castleMoveIfLegal, ← hc, h_rights, ↓reduceIte, h_king_at, h_rook_at,
             h_king, h_rook_pt, h_rook_color, and_self, true_and]
  -- The goal has: if (emptyAll && safeAll) then some {...} else none = some m
  -- where safeAll uses `!inCheck` but h_safe uses `¬inCheck` (decide form)
  -- Convert h_safe to the ! form
  have h_safe' : ((castleConfig m.piece.color kingSide).checkSquares.all fun sq =>
    !(inCheck (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update sq (some m.piece)) m.piece.color)) = true := by
    simp only [List.all_eq_true] at h_safe ⊢
    intro x hx
    have := h_safe x hx
    simp only [decide_eq_true_eq] at this
    cases hinc : (inCheck (gs.board.update (castleConfig m.piece.color kingSide).kingFrom none |>.update x (some m.piece)) m.piece.color)
    · rfl
    · exact absurd hinc this
  simp only [h_empty, h_safe', Bool.and_eq_true, and_self, ↓reduceIte]
  -- Goal: some { ... } = some m
  congr 1
  -- Goal: { piece := ..., fromSq := ..., ... } = m
  cases m
  simp only [Move.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (first | rfl | exact Eq.symm (by assumption) | (simp_all))

/--
King (castle) case of fideLegal_in_pieceTargets: if m is fideLegal, involves a king,
and IS a castle move, then the move is in pieceTargets.

This proves the castle King case of `fideLegal_in_pieceTargets_axiom`.
-/
theorem fideLegal_king_castle_in_pieceTargets (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_king : m.piece.pieceType = PieceType.King)
    (h_castle : m.isCastle = true) :
    m ∈ pieceTargets gs m.fromSq m.piece := by
  -- Use the axiom to get the kingSide
  obtain ⟨kingSide, h_produces⟩ := castleMoveIfLegal_produces_fideLegal gs m h_legal h_king h_castle
  -- Unfold pieceTargets for king
  unfold pieceTargets
  simp only [h_king]
  -- The result is standard ++ castles
  simp only [List.mem_append]
  right
  -- Now show m is in the castles list
  simp only [List.mem_filterMap, Option.mem_def]
  -- castles = [castleMoveIfLegal gs true, castleMoveIfLegal gs false].filterMap id
  refine ⟨some m, ?_, rfl⟩
  -- Show some m is in [castleMoveIfLegal gs true, castleMoveIfLegal gs false]
  simp only [List.mem_cons, List.mem_singleton]
  cases kingSide with
  | true => left; exact h_produces.symm
  | false => right; left; exact h_produces.symm

-- ============================================================================
-- Pawn Completeness
-- ============================================================================

/--
When isPawnAdvance holds, squareFromInts produces the target square.
This bridges the geometric predicate to the computational squareFromInts.
-/
theorem pawnAdvance_squareFromInts (c : Color) (src tgt : Square)
    (h_adv : Movement.isPawnAdvance c src tgt) :
    (Movement.rankDiff src tgt = -Movement.pawnDirection c →
      Movement.squareFromInts src.fileInt (src.rankInt + Movement.pawnDirection c) = some tgt) ∧
    (Movement.rankDiff src tgt = -2 * Movement.pawnDirection c →
      Movement.squareFromInts src.fileInt (src.rankInt + 2 * Movement.pawnDirection c) = some tgt) := by
  -- From isPawnAdvance: tgt is in same file and 1 or 2 ranks forward
  have h_file_eq := h_adv.2.1  -- fileDiff src tgt = 0, so src.fileInt = tgt.fileInt
  constructor
  · intro h_single
    -- For single-step advance: rankDiff = -pawnDirection
    -- rankDiff src tgt = src.rankInt - tgt.rankInt = -pawnDirection
    -- So tgt.rankInt = src.rankInt + pawnDirection
    unfold Movement.rankDiff at h_single
    unfold Movement.fileDiff at h_file_eq
    rw [show src.fileInt = tgt.fileInt by omega]
    rw [show src.rankInt + Movement.pawnDirection c = tgt.rankInt by omega]
    exact squareFromInts_roundTrip tgt
  · intro h_double
    -- For double-step advance: rankDiff = -2*pawnDirection
    -- rankDiff src tgt = src.rankInt - tgt.rankInt = -2*pawnDirection
    -- So tgt.rankInt = src.rankInt + 2*pawnDirection
    unfold Movement.rankDiff at h_double
    unfold Movement.fileDiff at h_file_eq
    rw [show src.fileInt = tgt.fileInt by omega]
    rw [show src.rankInt + 2 * Movement.pawnDirection c = tgt.rankInt by omega]
    exact squareFromInts_roundTrip tgt

/--
When isPawnCapture holds, squareFromInts with appropriate file offset produces the target square.
-/
theorem pawnCapture_squareFromInts (c : Color) (src tgt : Square)
    (h_cap : Movement.isPawnCapture c src tgt) :
    ∃ df : Int, df ∈ [-1, 1] ∧
      Movement.squareFromInts (src.fileInt + df) (src.rankInt + Movement.pawnDirection c) = some tgt := by
  -- From isPawnCapture: tgt is exactly 1 file away and 1 rank forward
  have h_fileDiff := h_cap.2.1  -- absInt (fileDiff src tgt) = 1
  have h_rankDiff := h_cap.2.2  -- rankDiff src tgt = pawnDirection c
  -- fileDiff src tgt = src.fileInt - tgt.fileInt, so absInt(src.fileInt - tgt.fileInt) = 1
  -- This means either src.fileInt - tgt.fileInt = 1 or src.fileInt - tgt.fileInt = -1
  -- Case 1: src.fileInt - tgt.fileInt = 1 → tgt.fileInt = src.fileInt - 1 → df = -1
  -- Case 2: src.fileInt - tgt.fileInt = -1 → tgt.fileInt = src.fileInt + 1 → df = 1
  by_cases h : Movement.fileDiff src tgt = 1
  · -- Case: src.fileInt - tgt.fileInt = 1, so df = -1
    refine ⟨-1, ?_, ?_⟩
    · decide
    · unfold Movement.fileDiff at h
      unfold Movement.rankDiff at h_rankDiff
      have h_rank_eq : src.rankInt + Movement.pawnDirection c = tgt.rankInt := by omega
      have h_file_eq : src.fileInt + (-1 : Int) = tgt.fileInt := by omega
      rw [h_rank_eq, h_file_eq]
      exact squareFromInts_roundTrip tgt
  · -- Case: src.fileInt - tgt.fileInt ≠ 1, but absInt(...) = 1, so src.fileInt - tgt.fileInt = -1
    refine ⟨1, ?_, ?_⟩
    · decide
    · unfold Movement.fileDiff at h_fileDiff h
      unfold Movement.absInt at h_fileDiff
      unfold Movement.rankDiff at h_rankDiff
      have h_rank_eq : src.rankInt + Movement.pawnDirection c = tgt.rankInt := by omega
      have h_file_eq : src.fileInt + 1 = tgt.fileInt := by omega
      rw [h_rank_eq, h_file_eq]
      exact squareFromInts_roundTrip tgt

/--
Theorem: For a single-step pawn advance, the target square must be empty.

This follows from:
1. Non-capture pawn moves (isCapture = false) don't target occupied enemy squares
2. destinationFriendlyFreeProp ensures no friendly pieces at target
3. Combined: target must be empty

Proof uses captureFlagConsistentWithEP and destinationFriendlyFreeProp from fideLegal.
-/
theorem pawnAdvance_singleStep_isEmpty (gs : GameState) (m : Move)
    (h_pawn : m.piece.pieceType = PieceType.Pawn)
    (h_adv : Movement.isPawnAdvance m.piece.color m.fromSq m.toSq)
    (h_single : Movement.rankDiff m.fromSq m.toSq = -Movement.pawnDirection m.piece.color)
    (h_path : pathClear gs.board m.fromSq m.toSq)
    (h_not_cap : m.isCapture = false)
    (h_cap_consistent : captureFlagConsistentWithEP gs m)
    (h_friendly_free : destinationFriendlyFreeProp gs m) :
    isEmpty gs.board m.toSq = true := by
  -- From captureFlagConsistentWithEP with isCapture = false:
  -- false = true ↔ (∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ m.isEnPassant
  -- So ¬((∃ p, enemy at target) ∨ isEnPassant)
  unfold captureFlagConsistentWithEP at h_cap_consistent
  rw [h_not_cap] at h_cap_consistent
  -- h_cap_consistent : false = true ↔ (∃ p, ...) ∨ m.isEnPassant
  have h_no_enemy_or_ep : ¬((∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ m.isEnPassant) := by
    intro h
    have := h_cap_consistent.mpr h
    exact Bool.noConfusion this
  have h_no_enemy : ¬(∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) :=
    fun h => h_no_enemy_or_ep (Or.inl h)
  -- From destinationFriendlyFreeProp: either empty or enemy at target
  unfold destinationFriendlyFreeProp at h_friendly_free
  unfold destinationFriendlyFree at h_friendly_free
  -- Case analysis on gs.board m.toSq
  unfold isEmpty
  cases h_board : gs.board m.toSq with
  | none => rfl
  | some p =>
    -- If there's a piece, it must be enemy (from h_friendly_free)
    simp only [h_board, decide_eq_true_eq] at h_friendly_free
    -- But h_no_enemy says no such enemy exists
    exfalso
    exact h_no_enemy ⟨p, h_board, h_friendly_free⟩

/--
Theorem: For a two-step pawn advance, both intermediate and target squares are empty.

The intermediate square is empty via pathClear (squaresBetween includes it for 2-step moves).
The target square emptiness follows from the same logic as single-step:
non-capture + captureFlagConsistentWithEP + destinationFriendlyFreeProp.
-/
theorem pawnAdvance_twoStep_isEmpty (gs : GameState) (m : Move)
    (h_pawn : m.piece.pieceType = PieceType.Pawn)
    (h_adv : Movement.isPawnAdvance m.piece.color m.fromSq m.toSq)
    (h_two : Movement.rankDiff m.fromSq m.toSq = -2 * Movement.pawnDirection m.piece.color)
    (h_path : pathClear gs.board m.fromSq m.toSq)
    (h_not_cap : m.isCapture = false)
    (h_cap_consistent : captureFlagConsistentWithEP gs m)
    (h_friendly_free : destinationFriendlyFreeProp gs m) :
    (∀ sq, Movement.squareFromInts m.fromSq.fileInt (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) = some sq →
      isEmpty gs.board sq = true) ∧
    isEmpty gs.board m.toSq = true := by
  constructor
  -- Part 1: Intermediate square is empty via pathClear
  · intro sq h_sq
    have ⟨intermediate, h_int_eq, h_int_empty⟩ :=
      pathClear_twoStep_intermediate gs.board m.fromSq m.toSq m.piece.color h_adv h_two h_path
    have h : some sq = some intermediate := h_sq.symm.trans h_int_eq
    rw [Option.some.injEq] at h
    rw [h]
    exact h_int_empty
  -- Part 2: Target square is empty (same proof as single-step)
  · unfold captureFlagConsistentWithEP at h_cap_consistent
    rw [h_not_cap] at h_cap_consistent
    have h_no_enemy_or_ep : ¬((∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) ∨ m.isEnPassant) := by
      intro h
      have := h_cap_consistent.mpr h
      exact Bool.noConfusion this
    have h_no_enemy : ¬(∃ p, gs.board m.toSq = some p ∧ p.color ≠ m.piece.color) :=
      fun h => h_no_enemy_or_ep (Or.inl h)
    unfold destinationFriendlyFreeProp at h_friendly_free
    unfold destinationFriendlyFree at h_friendly_free
    unfold isEmpty
    cases h_board : gs.board m.toSq with
    | none => rfl
    | some p =>
      simp only [h_board, decide_eq_true_eq] at h_friendly_free
      exfalso
      exact h_no_enemy ⟨p, h_board, h_friendly_free⟩

/--
Helper: A move without promotion has promotion = none.
-/
theorem pawn_nopromo_helper (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_pawn : m.piece.pieceType = PieceType.Pawn)
    (h_not_promo_rank : m.toSq.rankNat ≠ pawnPromotionRank m.piece.color) :
    m.promotion = none := by
  cases h_promo : m.promotion with
  | none => rfl
  | some _ =>
    have h_is_some : m.promotion.isSome = true := by simp [h_promo]
    have h_cond := h_legal.2.2.2.2.2.2.2.1 h_is_some
    exact absurd h_cond.2 h_not_promo_rank

/--
Axiom: En passant captures cannot happen on the promotion rank.
En passant occurs on ranks 3 (for Black) or 6 (for White), not on ranks 1 or 8.
-/
theorem enPassant_not_promo_rank (c : Color) (src tgt : Square)
    (h_cap : Movement.isPawnCapture c src tgt)
    (h_ep_rank : tgt.rankNat = 2 ∨ tgt.rankNat = 5) :  -- EP target ranks
    tgt.rankNat ≠ pawnPromotionRank c := by
  cases c with
  | White =>
    -- White: pawnPromotionRank = 7, EP targets = {2, 5}
    unfold pawnPromotionRank
    cases h_ep_rank with
    | inl h => simp [h]
    | inr h => simp [h]
  | Black =>
    -- Black: pawnPromotionRank = 0, EP targets = {2, 5}
    unfold pawnPromotionRank
    cases h_ep_rank with
    | inl h => simp [h]
    | inr h => simp [h]

/--
Helper: Membership in a foldr that appends function results.
If `b ∈ f a` for some `a ∈ xs`, then `b` is in the foldr result.
This captures the flatMap-like pattern used in pieceTargets.
-/
theorem mem_foldr_append {α β : Type} (f : α → List β) (xs : List α) (b : β)
    (h : ∃ a ∈ xs, b ∈ f a) : b ∈ xs.foldr (fun x acc => f x ++ acc) [] := by
  induction xs with
  | nil => obtain ⟨a, ha, _⟩ := h; cases ha
  | cons x xs ih =>
    obtain ⟨a, ha_mem, hb_in⟩ := h
    show b ∈ f x ++ xs.foldr (fun x acc => f x ++ acc) []
    rw [List.mem_append]
    rcases List.mem_cons.mp ha_mem with rfl | ha_tail
    · left; exact hb_in
    · right; exact ih ⟨a, ha_tail, hb_in⟩

/--
Theorem: Given the pawn advance and squareFromInts conditions, the move is in forwardMoves.
This bridges the computed squareFromInts results to the list membership via foldr.
-/
theorem pawnAdvance_in_forwardMoves (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_pawn : m.piece.pieceType = PieceType.Pawn)
    (h_adv : Movement.isPawnAdvance m.piece.color m.fromSq m.toSq)
    (h_path : pathClear gs.board m.fromSq m.toSq)
    (h_not_cap : m.isCapture = false)
    (h_not_ep : m.isEnPassant = false)
    (h_not_castle : m.isCastle = false)
    (h_cap_consistent : captureFlagConsistentWithEP gs m)
    (h_friendly_free : destinationFriendlyFreeProp gs m) :
    let dir := Movement.pawnDirection m.piece.color
    let oneStep := Movement.squareFromInts m.fromSq.fileInt (m.fromSq.rankInt + dir)
    let twoStep := Movement.squareFromInts m.fromSq.fileInt (m.fromSq.rankInt + 2 * dir)
    let forwardMoves : List Move :=
      match oneStep with
      | some target =>
          if isEmpty gs.board target then
            let base : List Move := [{ piece := m.piece, fromSq := m.fromSq, toSq := target }]
            let doubleStep : List Move :=
              if m.fromSq.rankNat = pawnStartRank m.piece.color then
                match twoStep with
                | some target2 =>
                    if isEmpty gs.board target2 then
                      [{ piece := m.piece, fromSq := m.fromSq, toSq := target2 }]
                    else
                      []
                | none => []
              else
                []
            base ++ doubleStep
          else
            []
      | none => []
    m ∈ forwardMoves.foldr (fun mv acc => promotionMoves mv ++ acc) [] := by
  -- Castle rook fields are none (from fideLegal, since ¬isCastle)
  have h_rook_none := h_legal.2.2.2.2.2.2.2.2.2.2.2.1 (by simp [h_not_castle])
  -- Case split: single-step vs two-step advance
  rcases h_adv.2.2 with h_single | h_double
  -- CASE 1: Single-step advance
  · have h_one := (pawnAdvance_squareFromInts m.piece.color m.fromSq m.toSq h_adv).1 h_single
    have h_empty := pawnAdvance_singleStep_isEmpty gs m h_pawn h_adv h_single h_path
      h_not_cap h_cap_consistent h_friendly_free
    let base : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq }
    have h_m_in_promo : m ∈ promotionMoves base := by
      unfold promotionMoves
      by_cases h_promo_rank : m.toSq.rankNat = pawnPromotionRank m.piece.color
      · -- On promotion rank: need m.promotion type ∈ promotionTargets
        have h_cond : base.piece.pieceType = PieceType.Pawn ∧
          base.toSq.rankNat = pawnPromotionRank base.piece.color := ⟨h_pawn, h_promo_rank⟩
        rw [if_pos h_cond]
        -- From fideLegal: pawn at promo rank → promotion.isSome
        have h_promo_fwd := h_legal.2.2.2.2.2.2.1
        have h_promo_some : m.promotion.isSome := h_promo_fwd ⟨h_pawn, h_promo_rank⟩
        -- From fideLegal: promotion.isSome → ∃ pt ∈ promotionTargets, promotion = some pt
        have h_promo_valid := h_legal.2.2.2.2.2.2.2.2.2.2.2.2 h_promo_some
        obtain ⟨pt, h_pt_mem, h_pt_eq⟩ := h_promo_valid
        simp only [List.mem_map]
        have ⟨h_rf, h_rt⟩ := h_rook_none
        exact ⟨pt, h_pt_mem, by
          cases m; simp only [Move.mk.injEq]
          exact ⟨rfl, rfl, rfl, h_not_cap.symm, h_pt_eq.symm, h_not_castle.symm,
                 h_rf.symm, h_rt.symm, h_not_ep.symm⟩⟩
      · -- Not on promotion rank: promotionMoves = [base], and m = base
        have h_not_cond : ¬(base.piece.pieceType = PieceType.Pawn ∧
          base.toSq.rankNat = pawnPromotionRank base.piece.color) :=
          fun ⟨_, h⟩ => h_promo_rank h
        rw [if_neg h_not_cond]
        have h_no_promo := pawn_nopromo_helper gs m h_legal h_pawn h_promo_rank
        have ⟨h_rf, h_rt⟩ := h_rook_none
        have h_m_eq : m = base := by
          cases m; congr 1 <;> assumption
        rw [h_m_eq]; exact List.mem_cons_self
    apply mem_foldr_append
    refine ⟨base, ?_, h_m_in_promo⟩
    simp only [h_one, h_empty, ↓reduceIte]
    exact List.mem_append_left _ List.mem_cons_self
  -- CASE 2: Two-step advance
  · have h_two_eq := (pawnAdvance_squareFromInts m.piece.color m.fromSq m.toSq h_adv).2 h_double
    have h_both := pawnAdvance_twoStep_isEmpty gs m h_pawn h_adv h_double h_path
      h_not_cap h_cap_consistent h_friendly_free
    have h_tgt_empty : isEmpty gs.board m.toSq = true := h_both.2
    -- Intermediate square exists and is empty
    have ⟨intermediate, h_int_eq, h_int_empty⟩ :=
      pathClear_twoStep_intermediate gs.board m.fromSq m.toSq m.piece.color h_adv h_double h_path
    -- Must be on start rank (from respectsGeometry two-step condition)
    have h_must_start : m.fromSq.rankNat = pawnStartRank m.piece.color := by
      have h_geom := h_legal.2.2.1
      unfold respectsGeometry at h_geom
      simp only [h_pawn, h_not_cap] at h_geom
      exact h_geom.2.2 h_double
    -- Two-step never reaches promotion rank
    have h_not_promo_rank : m.toSq.rankNat ≠ pawnPromotionRank m.piece.color := by
      intro h_eq
      unfold Movement.rankDiff at h_double
      simp only [Square.rankInt, Square.rankNat, Rank.toNat, Int.ofNat_eq_natCast] at h_double h_must_start h_eq
      cases hc : m.piece.color with
      | White =>
        simp only [hc, pawnPromotionRank, pawnStartRank, Movement.pawnDirection] at *
        omega
      | Black =>
        simp only [hc, pawnPromotionRank, pawnStartRank, Movement.pawnDirection] at *
        omega
    let base : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq }
    have h_m_in_promo : m ∈ promotionMoves base := by
      unfold promotionMoves
      have h_not_cond : ¬(base.piece.pieceType = PieceType.Pawn ∧
        base.toSq.rankNat = pawnPromotionRank base.piece.color) :=
        fun ⟨_, h⟩ => h_not_promo_rank h
      rw [if_neg h_not_cond]
      have h_no_promo := pawn_nopromo_helper gs m h_legal h_pawn h_not_promo_rank
      obtain ⟨h_rf, h_rt⟩ := h_rook_none
      have h_m_eq : m = base := by
        cases m; congr 1 <;> assumption
      rw [h_m_eq]; exact List.mem_cons_self
    apply mem_foldr_append
    refine ⟨base, ?_, h_m_in_promo⟩
    simp only [h_int_eq, h_int_empty, ↓reduceIte, h_must_start, h_two_eq, h_tgt_empty]
    exact List.mem_append_right _ List.mem_cons_self

/--
Theorem: Given the pawn capture and squareFromInts conditions, the move is in captureMoves.
This proves the move appears in the foldr-based capture list via case analysis on:
1. Capture geometry: which offset (-1 or 1) generates the target
2. Target condition: whether it's a regular capture (isEnemyAt) or en passant
-/
theorem pawnCapture_in_captureMoves (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_pawn : m.piece.pieceType = PieceType.Pawn)
    (h_cap : m.isCapture = true)
    (h_cap_geom : Movement.isPawnCapture m.piece.color m.fromSq m.toSq)
    (h_not_castle : m.isCastle = false)
    (h_target_cond : isEnemyAt gs.board m.piece.color m.toSq = true ∨
                     (gs.enPassantTarget = some m.toSq ∧ m.isEnPassant = true))
    (h_ep_empty : m.isEnPassant = true → isEmpty gs.board m.toSq = true)
    (h_ep_promo : m.isEnPassant = true → m.promotion = none) :
    let color := m.piece.color
    let dir := Movement.pawnDirection color
    let captureOffsets : List Int := [-1, 1]
    let captureMoves :=
      captureOffsets.foldr
        (fun df acc =>
          match Movement.squareFromInts (m.fromSq.fileInt + df) (m.fromSq.rankInt + dir) with
          | some target =>
              if isEnemyAt gs.board color target then
                promotionMoves { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true } ++ acc
              else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
                { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true, isEnPassant := true } :: acc
              else
                acc
          | none => acc)
        []
    m ∈ captureMoves := by
  have h_rook_none := h_legal.2.2.2.2.2.2.2.2.2.2.2.1 (by simp [h_not_castle])
  obtain ⟨df, h_df_mem, h_sq_eq⟩ := pawnCapture_squareFromInts m.piece.color m.fromSq m.toSq h_cap_geom
  cases h_ep : m.isEnPassant
  · -- Regular capture (m.isEnPassant = false)
    -- From h_target_cond, since m.isEnPassant = false, must have isEnemyAt = true
    have h_enemy : isEnemyAt gs.board m.piece.color m.toSq = true := by
      rcases h_target_cond with h | ⟨_, h_ep_true⟩
      · exact h
      · simp [h_ep] at h_ep_true
    let base : Move := { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq, isCapture := true }
    have h_m_in_promo : m ∈ promotionMoves base := by
      unfold promotionMoves
      by_cases h_promo_rank : m.toSq.rankNat = pawnPromotionRank m.piece.color
      · have h_cond : base.piece.pieceType = PieceType.Pawn ∧
          base.toSq.rankNat = pawnPromotionRank base.piece.color := ⟨h_pawn, h_promo_rank⟩
        rw [if_pos h_cond]
        -- From fideLegal: pawn at promo rank → promotion.isSome
        have h_promo_fwd := h_legal.2.2.2.2.2.2.1
        have h_promo_some : m.promotion.isSome := h_promo_fwd ⟨h_pawn, h_promo_rank⟩
        -- From fideLegal: promotion.isSome → ∃ pt ∈ promotionTargets, promotion = some pt
        have h_promo_valid := h_legal.2.2.2.2.2.2.2.2.2.2.2.2 h_promo_some
        obtain ⟨pt, h_pt_mem, h_pt_eq⟩ := h_promo_valid
        simp only [List.mem_map]
        obtain ⟨h_rf, h_rt⟩ := h_rook_none
        exact ⟨pt, h_pt_mem, by
          cases m; simp only [Move.mk.injEq]
          exact ⟨rfl, rfl, rfl, h_cap.symm, h_pt_eq.symm, h_not_castle.symm,
                 h_rf.symm, h_rt.symm, h_ep.symm⟩⟩
      · have h_not_cond : ¬(base.piece.pieceType = PieceType.Pawn ∧
          base.toSq.rankNat = pawnPromotionRank base.piece.color) :=
          fun ⟨_, h⟩ => h_promo_rank h
        rw [if_neg h_not_cond]
        have h_no_promo := pawn_nopromo_helper gs m h_legal h_pawn h_promo_rank
        obtain ⟨h_rf, h_rt⟩ := h_rook_none
        have h_m_eq : m = base := by
          cases m; congr 1 <;> assumption
        rw [h_m_eq]; exact List.mem_cons_self
    -- Foldr membership: show the step for our df produces m, and foldr preserves it
    -- Monotonicity: if mv ∈ acc then mv ∈ step x acc (for any x)
    have h_mono : ∀ (x : Int) (acc : List Move) (mv : Move), mv ∈ acc →
      mv ∈ (match Movement.squareFromInts (m.fromSq.fileInt + x)
              (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) with
        | some target =>
          if isEnemyAt gs.board m.piece.color target then
            promotionMoves { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
            { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true,
              isEnPassant := true } :: acc
          else acc
        | none => acc) := by
      intro x acc mv h_in
      split
      · split
        · exact List.mem_append_right _ h_in
        · split
          · exact List.mem_cons_of_mem _ h_in
          · exact h_in
      · exact h_in
    -- Step with our df produces m (for any acc)
    have h_step : ∀ (acc : List Move), m ∈
      (match Movement.squareFromInts (m.fromSq.fileInt + df)
              (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) with
        | some target =>
          if isEnemyAt gs.board m.piece.color target then
            promotionMoves { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
            { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true,
              isEnPassant := true } :: acc
          else acc
        | none => acc) := by
      intro acc
      simp only [h_sq_eq, h_enemy, ↓reduceIte]
      exact List.mem_append_left _ h_m_in_promo
    -- Unfold foldr for [-1, 1] and combine
    show m ∈ ([-1, 1] : List Int).foldr (fun df' acc =>
      match Movement.squareFromInts (m.fromSq.fileInt + df')
              (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) with
        | some target =>
          if isEnemyAt gs.board m.piece.color target then
            promotionMoves { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
            { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true,
              isEnPassant := true } :: acc
          else acc
        | none => acc) []
    simp only [List.foldr_cons, List.foldr_nil]
    rcases List.mem_cons.mp h_df_mem with rfl | h_tail
    · -- df = -1: m is in the outer step directly
      exact h_step _
    · -- df must be 1
      rcases List.mem_cons.mp h_tail with rfl | h_nil
      · -- df = 1: m is in the inner step, monotonicity preserves it in the outer
        exact h_mono (-1) _ _ (h_step [])
      · cases h_nil
  · -- EP capture (m.isEnPassant = true)
    have h_ep_emp := h_ep_empty h_ep
    have h_promo := h_ep_promo h_ep
    -- isEmpty means the square has no piece
    have h_board_none : gs.board m.toSq = none := by
      unfold isEmpty at h_ep_emp
      exact of_decide_eq_true h_ep_emp
    -- No piece means not enemy
    have h_not_enemy : isEnemyAt gs.board m.piece.color m.toSq = false := by
      simp only [isEnemyAt, h_board_none]
    -- Get EP target from h_target_cond
    have h_ep_tgt : gs.enPassantTarget = some m.toSq := by
      rcases h_target_cond with h_enemy | ⟨h, _⟩
      · simp [h_not_enemy] at h_enemy
      · exact h
    -- Move equality: m equals the EP move literal
    obtain ⟨h_rf, h_rt⟩ := h_rook_none
    have h_m_eq : m = { piece := m.piece, fromSq := m.fromSq, toSq := m.toSq,
        isCapture := true, isEnPassant := true } := by
      cases m; simp only [Move.mk.injEq]
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (first | rfl | exact Eq.symm (by assumption) | simp_all)
    -- Monotonicity: membership is preserved through foldr steps
    have h_mono : ∀ (x : Int) (acc : List Move) (mv : Move), mv ∈ acc →
      mv ∈ (match Movement.squareFromInts (m.fromSq.fileInt + x)
              (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) with
        | some target =>
          if isEnemyAt gs.board m.piece.color target then
            promotionMoves { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
            { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true,
              isEnPassant := true } :: acc
          else acc
        | none => acc) := by
      intro x acc mv h_in
      split
      · split
        · exact List.mem_append_right _ h_in
        · split
          · exact List.mem_cons_of_mem _ h_in
          · exact h_in
      · exact h_in
    -- Step: our specific df produces m in the EP branch
    have h_step : ∀ (acc : List Move), m ∈
      (match Movement.squareFromInts (m.fromSq.fileInt + df)
              (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) with
        | some target =>
          if isEnemyAt gs.board m.piece.color target then
            promotionMoves { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
            { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true,
              isEnPassant := true } :: acc
          else acc
        | none => acc) := by
      intro acc
      simp only [h_sq_eq, h_not_enemy, ↓reduceIte]
      rw [if_pos ⟨h_ep_tgt, h_ep_emp⟩]
      rw [← h_m_eq]
      exact List.mem_cons_self _ _
    -- Unfold foldr for [-1, 1] and combine
    show m ∈ ([-1, 1] : List Int).foldr (fun df' acc =>
      match Movement.squareFromInts (m.fromSq.fileInt + df')
              (m.fromSq.rankInt + Movement.pawnDirection m.piece.color) with
        | some target =>
          if isEnemyAt gs.board m.piece.color target then
            promotionMoves { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true } ++ acc
          else if gs.enPassantTarget = some target ∧ isEmpty gs.board target then
            { piece := m.piece, fromSq := m.fromSq, toSq := target, isCapture := true,
              isEnPassant := true } :: acc
          else acc
        | none => acc) []
    simp only [List.foldr_cons, List.foldr_nil]
    rcases List.mem_cons.mp h_df_mem with rfl | h_tail
    · exact h_step _
    · rcases List.mem_cons.mp h_tail with rfl | h_nil
      · exact h_mono (-1) _ _ (h_step [])
      · cases h_nil

/--
Pawn case of fideLegal_in_pieceTargets: if m is fideLegal and involves a pawn,
then the move is in pieceTargets.

This proves the Pawn case of `fideLegal_in_pieceTargets_axiom`.
-/
theorem fideLegal_pawn_in_pieceTargets (gs : GameState) (m : Move)
    (h_legal : fideLegal gs m)
    (h_pawn : m.piece.pieceType = PieceType.Pawn) :
    m ∈ pieceTargets gs m.fromSq m.piece := by
  -- Extract geometry from fideLegal
  have h_geom := h_legal.2.2.1
  unfold respectsGeometry at h_geom
  simp only [h_pawn] at h_geom
  -- Pawns don't castle
  have h_not_castle : m.isCastle = false := by
    cases h_cb : m.isCastle with
    | false => rfl
    | true =>
      have h_king := h_legal.2.2.2.2.2.2.2.2.2.2.1 h_cb
      rw [h_pawn] at h_king
      exact PieceType.noConfusion h_king
  -- Unfold pieceTargets
  unfold pieceTargets
  simp only [h_pawn]
  -- The result is forwardMoves.foldr promotionMoves ++ captureMoves
  simp only [List.mem_append]
  -- Case split on capture vs non-capture
  by_cases h_cap : m.isCapture = true
  · -- Capture case
    right
    by_cases h_ep : m.isEnPassant = true
    · -- En passant capture
      simp only [h_cap, ↓reduceIte, h_ep] at h_geom
      have h_cap_geom := h_geom.1
      have h_ep_target := h_geom.2
      exact pawnCapture_in_captureMoves gs m h_legal h_pawn h_cap h_cap_geom h_not_castle
        (Or.inr ⟨h_ep_target.1, h_ep⟩) (fun _ => h_ep_target.2.1) (fun _ => h_ep_target.2.2)
    · -- Regular capture (not en passant)
      simp only [h_cap, ↓reduceIte, h_ep, Bool.false_eq_true] at h_geom
      have h_cap_geom := h_geom.1
      have h_enemy := h_geom.2
      exact pawnCapture_in_captureMoves gs m h_legal h_pawn h_cap h_cap_geom h_not_castle
        (Or.inl h_enemy) (fun h_is_ep => absurd h_is_ep h_ep) (fun h_is_ep => absurd h_is_ep h_ep)
  · -- Non-capture case (advance)
    left
    simp only [Bool.not_eq_true] at h_cap
    simp only [h_cap, Bool.false_eq_true, ↓reduceIte] at h_geom
    have h_adv := h_geom.1
    have h_path := h_geom.2.1
    -- Not en passant (non-capture)
    have h_not_ep : m.isEnPassant = false := by
      cases h_ep_b : m.isEnPassant with
      | false => rfl
      | true =>
        have h_cap_consistent' := h_legal.2.2.2.2.1
        unfold captureFlagConsistentWithEP at h_cap_consistent'
        have h_must_cap := h_cap_consistent'.mpr (Or.inr h_ep_b)
        rw [h_cap] at h_must_cap
        exact Bool.noConfusion h_must_cap
    -- Extract captureFlagConsistentWithEP and destinationFriendlyFreeProp from fideLegal
    have h_cap_consistent : captureFlagConsistentWithEP gs m := h_legal.2.2.2.2.1
    have h_friendly_free : destinationFriendlyFreeProp gs m := h_legal.2.2.2.1
    exact pawnAdvance_in_forwardMoves gs m h_legal h_pawn h_adv h_path h_cap h_not_ep h_not_castle h_cap_consistent h_friendly_free

-- ============================================================================
-- Combined Completeness Theorems
-- ============================================================================

/--
pieceTargets generates all fideLegal moves (modulo promotion choice).
The proof uses case analysis on piece type, applying the per-piece theorems above.
-/
theorem fideLegal_in_pieceTargets_axiom (gs : GameState) (m : Move) :
    fideLegal gs m →
    (∃ m' ∈ pieceTargets gs m.fromSq m.piece,
      m'.fromSq = m.fromSq ∧ m'.toSq = m.toSq ∧ m'.piece = m.piece ∧
      (m.piece.pieceType ≠ PieceType.Pawn ∨ m'.promotion = none → m' = m)) := by
  intro h_legal
  have h_mem : m ∈ pieceTargets gs m.fromSq m.piece := by
    cases h_pt : m.piece.pieceType with
    | King =>
      cases h_castle : m.isCastle with
      | false => exact fideLegal_king_noCastle_in_pieceTargets gs m h_legal h_pt h_castle
      | true => exact fideLegal_king_castle_in_pieceTargets gs m h_legal h_pt h_castle
    | Knight => exact fideLegal_knight_in_pieceTargets gs m h_legal h_pt
    | Rook => exact fideLegal_rook_in_pieceTargets gs m h_legal h_pt
    | Bishop => exact fideLegal_bishop_in_pieceTargets gs m h_legal h_pt
    | Queen => exact fideLegal_queen_in_pieceTargets gs m h_legal h_pt
    | Pawn => exact fideLegal_pawn_in_pieceTargets gs m h_legal h_pt
  exact ⟨m, h_mem, rfl, rfl, rfl, fun _ => rfl⟩

/--
For fideLegal moves with consistent flags, the exact move is in pieceTargets.
-/
theorem fideLegal_exact_in_pieceTargets (gs : GameState) (m : Move) :
    fideLegal gs m →
    captureFlagConsistent gs m →
    (m.promotion.isSome → m.toSq.rankNat = pawnPromotionRank m.piece.color) →
    m ∈ pieceTargets gs m.fromSq m.piece := by
  intro h_legal _h_cap _h_promo
  cases h_pt : m.piece.pieceType with
  | King =>
    cases h_castle : m.isCastle with
    | false => exact fideLegal_king_noCastle_in_pieceTargets gs m h_legal h_pt h_castle
    | true => exact fideLegal_king_castle_in_pieceTargets gs m h_legal h_pt h_castle
  | Knight => exact fideLegal_knight_in_pieceTargets gs m h_legal h_pt
  | Rook => exact fideLegal_rook_in_pieceTargets gs m h_legal h_pt
  | Bishop => exact fideLegal_bishop_in_pieceTargets gs m h_legal h_pt
  | Queen => exact fideLegal_queen_in_pieceTargets gs m h_legal h_pt
  | Pawn => exact fideLegal_pawn_in_pieceTargets gs m h_legal h_pt

-- ============================================================================
-- Phase 2: Board Invariant Preservation (TODO)
-- ============================================================================
-- The following theorems about movePiece require careful work with the
-- if-then-else structure in GameState.movePiece. Deferred for future work.
--
-- movePiece_clears_enPassant_non_twoStep: Non-pawn/single-step clears EP
-- movePiece_sets_enPassant_twoStep: Two-step sets EP to intermediate rank
-- movePiece_preserves_single_occupancy: At most one piece per square

end Chess.Rules
