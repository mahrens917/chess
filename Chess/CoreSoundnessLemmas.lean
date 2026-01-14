/-
CoreSoundnessLemmas.lean

This file defines core soundness lemmas that extract facts about legal moves from
the `encodedLegal` predicate. These lemmas are used by SemanticFideLegalSoundness.lean
to prove that all moves in allLegalMoves satisfy fideLegalSemantic.

This file exists to break a circular dependency:
- Completeness.lean needs SemanticFideLegalSoundness.lean for allLegalMoves_sound
- SemanticFideLegalSoundness.lean needs these core lemmas
- By putting these lemmas in a separate file, we break the cycle
-/

import Chess.RulesComplete
import Chess.SemanticRespectsGeometryLemmas
-- Note: SemanticCaptureFlagLemmas depends on Spec which has build issues
-- The lemma captureFlagConsistentWithEP_of_destinationFriendlyFree_and_captureFlagConsistent
-- is defined there, but we'll use sorry for now until Spec is fixed

namespace Chess
namespace Rules

/--
Core soundness lemma: Extracts the basic legality facts from allLegalMoves membership.
Returns a tuple of:
- `m.piece.color = gs.toMove` (turn matches)
- `gs.board m.fromSq = some m.piece` (piece at origin)
- `destinationFriendlyFreeProp gs m` (destination is free of friendly pieces)
- `inCheck (gs.movePiece m).board gs.toMove = false` (king is safe after move)
-/
theorem allLegalMoves_sound_fideLegalCore (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    m.piece.color = gs.toMove ∧
    gs.board m.fromSq = some m.piece ∧
    destinationFriendlyFreeProp gs m ∧
    inCheck (gs.movePiece m).board gs.toMove = false := by
  intro hMem
  have hEnc := (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨sq, p, hBoard, hColor, hTargets, _hPin, hSafe⟩
  -- Extract piece and square from pieceTargets
  have hNoCastle : m.isCastle = false ∨ m.isCastle = true := by
    cases hIs : m.isCastle <;> simp [hIs]
  -- For non-castle moves, the piece and fromSq come from pieceTargets structure
  -- For castle moves, they come from castleMoveIfLegal
  have hPieceFrom : m.piece = p ∧ m.fromSq = sq := by
    cases hNoCastle with
    | inl hNC =>
        exact Chess.Parsing.mem_pieceTargets_piece_fromSq_of_not_castle gs sq p m hTargets hNC
    | inr hCastle =>
        have hEx := Chess.Parsing.mem_pieceTargets_castle_exists gs sq p m hTargets hCastle
        rcases hEx with ⟨kingSide, hCM⟩
        exact ⟨Chess.Parsing.castleMoveIfLegal_piece gs kingSide m hCM,
               Chess.Parsing.castleMoveIfLegal_fromSq gs kingSide m hCM⟩
  -- Construct the result tuple
  have hTurn : m.piece.color = gs.toMove := by
    rw [hPieceFrom.1]
    exact hColor
  have hFrom : gs.board m.fromSq = some m.piece := by
    rw [hPieceFrom.1, hPieceFrom.2]
    exact hBoard
  have hDestFree : destinationFriendlyFreeProp gs m := by
    -- destinationFriendlyFree = true follows from basicLegalAndSafe
    unfold destinationFriendlyFreeProp
    have hBasic : basicMoveLegalBool gs m = true := by
      unfold basicLegalAndSafe at hSafe
      cases hB : basicMoveLegalBool gs m <;> simp [hB] at hSafe
      rfl
    unfold basicMoveLegalBool at hBasic
    simp only [Bool.and_eq_true] at hBasic
    exact hBasic.2.1
  have hSafeKing : inCheck (gs.movePiece m).board gs.toMove = false := by
    unfold basicLegalAndSafe at hSafe
    cases hB : basicMoveLegalBool gs m <;> simp [hB] at hSafe
    · cases hSafe
    · cases hChk : inCheck (gs.movePiece m).board gs.toMove <;> simp [hChk] at hSafe
      rfl
  exact ⟨hTurn, hFrom, hDestFree, hSafeKing⟩

/--
Soundness lemma: Every move in allLegalMoves respects the geometry constraints.
This follows from pieceTargets generating moves that respect piece movement rules.
-/
theorem allLegalMoves_sound_respectsGeometry (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    respectsGeometry gs m := by
  intro hMem
  have hEnc := (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨sq, p, _hBoard, _hColor, hTargets, _hPin, _hSafe⟩
  -- The move comes from pieceTargets, which generates geometrically valid moves
  exact respectsGeometry_of_pieceTargets gs sq p m hTargets

/--
Soundness lemma: Every move in allLegalMoves has consistent capture flag with en passant.
This combines captureFlagConsistent from basicLegalAndSafe with destinationFriendlyFree.

The proof follows from:
1. basicLegalAndSafe includes captureFlagConsistent = true
2. basicLegalAndSafe includes destinationFriendlyFree = true
3. These two together imply captureFlagConsistentWithEP
-/
theorem allLegalMoves_sound_captureFlagConsistentWithEP (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    captureFlagConsistentWithEP gs m := by
  intro hMem
  -- Extract the encodedLegal predicate from membership
  have hEnc := (mem_allLegalMoves_iff_encodedLegal gs m).1 hMem
  rcases hEnc with ⟨_sq, _p, _hBoard, _hColor, _hTargets, _hPin, hSafe⟩
  -- Extract basicMoveLegalBool from basicLegalAndSafe
  have hBasic : basicMoveLegalBool gs m = true := by
    unfold basicLegalAndSafe at hSafe
    cases hB : basicMoveLegalBool gs m <;> simp [hB] at hSafe
    rfl
  -- Extract destinationFriendlyFree and captureFlagConsistent from basicMoveLegalBool
  unfold basicMoveLegalBool at hBasic
  simp only [Bool.and_eq_true] at hBasic
  have _hDestFree : destinationFriendlyFreeProp gs m := hBasic.2.1
  have _hCapFlag : captureFlagConsistent gs m = true := hBasic.2.2.1
  -- The full proof requires SemanticCaptureFlagLemmas.lean which depends on Spec.lean
  -- Spec.lean currently has build issues that need to be resolved separately
  -- The proof would use: captureFlagConsistentWithEP_of_destinationFriendlyFree_and_captureFlagConsistent
  sorry

end Rules
end Chess
