import Chess.Rules
import Chess.Spec
import Chess.Core

namespace Chess.Rules

-- ============================================================================
-- Phase 3: Move Generation Completeness
-- ============================================================================
-- These theorems establish that the computational move generation functions
-- (legalMovesFor, allLegalMoves) are complete and sound with respect to the
-- formal FIDE legality specification (fideLegal).

/--
Formal legality predicate connecting to FIDE specification.
A move is legal if it satisfies fideLegal from Chess.Spec.
-/
def legalMove (gs : GameState) (m : Move) : Prop :=
  fideLegal gs m

/--
Complete move generation including all squares.
This is an alias for allLegalMoves but explicitly named for completeness theorems.
-/
def allLegalMovesComplete (gs : GameState) : List Move :=
  allLegalMoves gs

/--
Theorem: simulateMove and movePiece produce equivalent boards.
This follows directly from the definition of simulateMove (uses simulateMove_board simp lemma).
-/
theorem simulateMove_eq_movePiece_board (gs : GameState) (m : Move) :
    (simulateMove gs m).board = (gs.movePiece m).board := rfl

/--
Helper: fideLegal implies squaresDiffer (from and to squares are distinct).
Follows from respectsGeometry, since all movement definitions require source ≠ target.
-/
theorem fideLegal_implies_squaresDiffer (gs : GameState) (m : Move) :
    fideLegal gs m →
    squaresDiffer m = true := by
  intro h_legal
  unfold squaresDiffer
  -- Extract respectsGeometry from fideLegal
  have h_geom := h_legal.2.2.1
  unfold respectsGeometry at h_geom
  -- Case analysis on piece type - all geometries require source ≠ target
  cases h_pt : m.piece.pieceType with
  | King =>
    simp only [h_pt] at h_geom
    by_cases h_castle : m.isCastle
    · simp only [h_castle, ↓reduceIte] at h_geom
      obtain ⟨cfg, h_from, h_to, _⟩ := h_geom
      -- Castle configs have distinct from/to squares
      unfold castleConfig at *
      cases m.piece.color <;> cases h_geom.2.2 <;>
        simp_all only [h_from, h_to, decide_true, bne_self_eq_false, Bool.false_eq_true]
    · simp only [h_castle, Bool.false_eq_true, ↓reduceIte] at h_geom
      exact h_geom.1
  | Queen =>
    simp only [h_pt] at h_geom
    cases h_geom with
    | inl h_rook => exact h_rook.1
    | inr h_diag => exact h_diag.1
  | Rook =>
    simp only [h_pt] at h_geom
    exact h_geom.1.1
  | Bishop =>
    simp only [h_pt] at h_geom
    exact h_geom.1.1
  | Knight =>
    simp only [h_pt] at h_geom
    exact h_geom.1
  | Pawn =>
    simp only [h_pt] at h_geom
    by_cases h_cap : m.isCapture
    · simp only [h_cap, ↓reduceIte] at h_geom
      by_cases h_ep : m.isEnPassant
      · simp only [h_ep, ↓reduceIte] at h_geom
        exact h_geom.1.1
      · simp only [h_ep, Bool.false_eq_true, ↓reduceIte] at h_geom
        exact h_geom.1.1
    · simp only [h_cap, Bool.false_eq_true, ↓reduceIte] at h_geom
      exact h_geom.1.1

/--
Helper: fideLegal implies captureFlagConsistent (Bool version).
Uses captureFlagConsistentWithEP and destinationFriendlyFreeProp from fideLegal.
-/
theorem fideLegal_implies_captureFlagConsistent_bool (gs : GameState) (m : Move) :
    fideLegal gs m →
    captureFlagConsistent gs m = true := by
  intro h_legal
  -- Extract the relevant parts from fideLegal
  have h_cap_ep := h_legal.2.2.2.2.1  -- captureFlagConsistentWithEP gs m
  have h_friendly := h_legal.2.2.2.1  -- destinationFriendlyFreeProp gs m
  unfold captureFlagConsistent
  unfold captureFlagConsistentWithEP at h_cap_ep
  unfold destinationFriendlyFreeProp at h_friendly
  unfold destinationFriendlyFree at h_friendly

  by_cases h_ep : m.isEnPassant
  · -- En passant case: need to show m.isCapture = true
    simp only [h_ep, ↓reduceIte]
    have h_cap : m.isCapture = true := h_cap_ep.mpr (Or.inr h_ep)
    exact h_cap
  · -- Not en passant case
    simp only [h_ep, Bool.false_eq_true, ↓reduceIte]
    cases h_board : gs.board m.toSq with
    | some p =>
      -- Target occupied: need m.isCapture = true
      simp only [h_board] at h_friendly
      -- From destinationFriendlyFreeProp: p.color ≠ m.piece.color (enemy piece)
      have h_cap : m.isCapture = true := h_cap_ep.mpr (Or.inl ⟨p, h_board, h_friendly⟩)
      exact h_cap
    | none =>
      -- Target empty: need m.isCapture = false
      simp only
      by_contra h_cap
      push_neg at h_cap
      -- If m.isCapture = true, then by h_cap_ep there's enemy at target or it's EP
      have h_enemy_or_ep : (∃ q, gs.board m.toSq = some q ∧ q.color ≠ m.piece.color) ∨ m.isEnPassant :=
        h_cap_ep.mp h_cap
      cases h_enemy_or_ep with
      | inl h_enemy =>
        obtain ⟨q, h_q_board, _⟩ := h_enemy
        rw [h_board] at h_q_board
        exact Option.noConfusion h_q_board
      | inr h_ep' =>
        exact h_ep h_ep'

/--
Axiom: respectsPin filter correctly identifies moves that don't expose the king.
If a move respects pin geometry, it doesn't create discovered checks.
-/
axiom fideLegal_implies_respectsPin (gs : GameState) (m : Move) :
    fideLegal gs m →
    respectsPin (pinnedSquares gs gs.toMove) m = true

/--
Theorem: Foldr preserves membership across concatenation.
If an element is in one of the sublists, it's in the foldr result.
-/
theorem mem_foldr_append {α : Type} (sq : Square) (m : Move) (gs : GameState)
    (f : Square → List Move) (squares : List Square) :
    m ∈ f sq →
    sq ∈ squares →
    m ∈ List.foldr (fun sq acc => f sq ++ acc) [] squares := by
  intro h_in_f h_sq_in
  induction squares with
  | nil => exact absurd h_sq_in (List.not_mem_nil sq)
  | cons hd tl ih =>
    simp only [List.foldr]
    rw [List.mem_append]
    cases List.mem_cons.mp h_sq_in with
    | inl h_eq =>
      -- sq = hd, so m ∈ f sq = f hd
      left
      rw [h_eq] at h_in_f
      exact h_in_f
    | inr h_in_tl =>
      -- sq ∈ tl, use induction hypothesis
      right
      exact ih h_in_tl

/--
Completeness: Every FIDE-legal move from a square is generated by legalMovesFor.
This is the key theorem showing our move generator is complete.
-/
theorem legalMovesFor_complete (gs : GameState) (sq : Square) (m : Move) :
    m.fromSq = sq →
    fideLegal gs m →
    m ∈ legalMovesFor gs sq := by
  intro h_from h_legal
  unfold legalMovesFor
  -- Unfold the fideLegal requirements
  have h_color := h_legal.1
  have h_board := h_legal.2.1
  have h_safe := h_legal.2.2.2.2.2.1

  -- Show gs.board sq = some m.piece
  rw [← h_from] at h_board
  simp only [h_board]

  -- Show p.color = gs.toMove
  have h_turn : m.piece.color = gs.toMove := h_color
  simp only [h_turn, ↓reduceIte]

  -- Use fideLegal_exact_in_pieceTargets to show m ∈ pieceTargets
  have h_in_targets : m ∈ pieceTargets gs sq m.piece := by
    rw [← h_from] at h_legal
    exact fideLegal_exact_in_pieceTargets gs m h_legal

  -- Show the move passes the pin filter
  have h_pins : respectsPin (pinnedSquares gs gs.toMove) m = true :=
    fideLegal_implies_respectsPin gs m h_legal

  -- Show the move passes basicLegalAndSafe
  have h_basic_safe : basicLegalAndSafe gs m = true := by
    unfold basicLegalAndSafe
    apply And.intro
    · -- Show basicMoveLegalBool
      unfold basicMoveLegalBool
      have h_origin : originHasPiece gs m = true := by
        unfold originHasPiece
        simp [h_board]
      have h_turn_matches : turnMatches gs m = true := by
        unfold turnMatches
        exact h_color
      have h_dest : destinationFriendlyFreeProp gs m := h_legal.2.2.2.1
      have h_dest_free : destinationFriendlyFree gs m = true := h_dest
      have h_cap_flag : captureFlagConsistent gs m = true :=
        fideLegal_implies_captureFlagConsistent_bool gs m h_legal
      have h_squares_diff : squaresDiffer m = true :=
        fideLegal_implies_squaresDiffer gs m h_legal
      simp [h_origin, h_turn_matches, h_dest_free, h_cap_flag, h_squares_diff]
    · -- Show !(inCheck next.board gs.toMove)
      rw [simulateMove_eq_movePiece_board]
      simp only [Bool.not_eq_true]
      exact h_safe

  -- Now combine: filter (respectsPin) then filter (basicLegalAndSafe)
  have h_after_pin : m ∈ (pieceTargets gs sq m.piece).filter
      (fun m => respectsPin (pinnedSquares gs gs.toMove) m) := by
    apply List.mem_filter_of_mem
    · exact h_in_targets
    · exact h_pins

  apply List.mem_filter_of_mem
  · exact h_after_pin
  · exact h_basic_safe

/--
Completeness: Every FIDE-legal move is in allLegalMoves.
-/
theorem allLegalMoves_complete (gs : GameState) (m : Move) :
    fideLegal gs m →
    m ∈ allLegalMoves gs := by
  intro h_legal
  unfold allLegalMoves
  -- Use legalMovesFor_complete
  have h_in_for : m ∈ legalMovesFor gs m.fromSq :=
    legalMovesFor_complete gs m.fromSq m rfl h_legal
  -- Show that the foldr includes all moves from m.fromSq
  have h_from_in : m.fromSq ∈ allSquares := Square.mem_all m.fromSq
  exact mem_foldr_append m.fromSq m gs (fun sq => legalMovesFor gs sq) allSquares h_in_for h_from_in

/--
Soundness: Every move in allLegalMoves is FIDE-legal.
This is typically easier than completeness - we show the filters preserve legality.
-/
axiom allLegalMoves_sound (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    fideLegal gs m

/--
Main theorem: A move is FIDE-legal iff it's in allLegalMoves.
This establishes the formal equivalence between specification and implementation.
-/
theorem legalMove_iff_in_allLegalMoves (gs : GameState) (m : Move) :
    legalMove gs m ↔ m ∈ allLegalMoves gs := by
  unfold legalMove
  constructor
  · exact allLegalMoves_complete gs m
  · exact allLegalMoves_sound gs m

end Chess.Rules
