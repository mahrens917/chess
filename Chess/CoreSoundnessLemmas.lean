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

import Chess.Rules
import Chess.Spec
import Chess.Parsing_SAN_Proofs
import Chess.SemanticRespectsGeometryLemmas
import Chess.SemanticCaptureFlagLemmas

namespace Chess
namespace Rules

/--
Core soundness lemma: Extracts the basic legality facts from allLegalMoves membership.
Returns a tuple of:
- `m.piece.color = gs.toMove` (turn matches)
- `gs.board m.fromSq = some m.piece` (piece at origin)
- `destinationFriendlyFreeProp gs m` (destination is free of friendly pieces)
- `inCheck (gs.movePiece m).board gs.toMove = false` (king is safe after move)

NOTE: The `gs.board m.fromSq = some m.piece` condition requires `hasValidKings gs.board`
because it depends on the axiom `allLegalMoves_originHasPiece` from Parsing_SAN_Proofs.
-/
theorem allLegalMoves_sound_fideLegalCore (gs : GameState) (m : Move)
    (hValid : Parsing.hasValidKings gs.board) :
    m ∈ allLegalMoves gs →
    m.piece.color = gs.toMove ∧
    gs.board m.fromSq = some m.piece ∧
    destinationFriendlyFreeProp gs m ∧
    inCheck (gs.movePiece m).board gs.toMove = false := by
  intro hMem
  -- Extract basicLegalAndSafe from membership
  have hSafe : basicLegalAndSafe gs m = true :=
    Parsing.mem_allLegalMoves_implies_basicLegalAndSafe gs m hMem
  unfold basicLegalAndSafe at hSafe
  simp only [Bool.and_eq_true] at hSafe
  -- hSafe.1 : basicMoveLegalBool gs m = true
  -- hSafe.2 : !(inCheck ...) = true, i.e., inCheck ... = false
  have hBasic := hSafe.1
  have hKingSafe : inCheck (gs.movePiece m).board gs.toMove = false := by
    have h := hSafe.2
    simp only [Bool.not_eq_true'] at h
    exact h
  -- Unfold basicMoveLegalBool to get individual conditions
  unfold basicMoveLegalBool at hBasic
  simp only [Bool.and_eq_true] at hBasic
  obtain ⟨⟨⟨⟨_hOrigin, hTurn⟩, hDestFree⟩, _hCapFlag⟩, _hDiff⟩ := hBasic
  -- Extract turn matches
  have hTurnEq : m.piece.color = gs.toMove := by
    unfold turnMatches at hTurn
    simp only [decide_eq_true_eq] at hTurn
    exact hTurn
  -- Extract board origin using the axiom
  have hBoardOrigin : gs.board m.fromSq = some m.piece :=
    Parsing.allLegalMoves_originHasPiece gs m hValid hMem
  -- destinationFriendlyFreeProp is just destinationFriendlyFree = true
  have hDestFreeProp : destinationFriendlyFreeProp gs m := by
    unfold destinationFriendlyFreeProp
    exact hDestFree
  exact ⟨hTurnEq, hBoardOrigin, hDestFreeProp, hKingSafe⟩

-- respectsGeometry_of_pieceTargets is imported from Chess.SemanticRespectsGeometryLemmas

/--
Helper: membership in legalMovesForCached implies encodedLegal structure.
-/
private theorem mem_legalMovesForCached_implies_encodedLegal
    (gs : GameState) (sq : Square) (pins : List (Square × Square)) (m : Move) :
    m ∈ legalMovesForCached gs sq pins →
    ∃ p,
      gs.board sq = some p ∧
      p.color = gs.toMove ∧
      m ∈ pieceTargets gs sq p ∧
      respectsPin pins m = true ∧
      basicLegalAndSafe gs m = true := by
  intro hmem
  unfold legalMovesForCached at hmem
  split at hmem
  · simp at hmem
  · rename_i p heq
    split at hmem
    · simp at hmem
    · rename_i hcolor
      -- hcolor : ¬p.color ≠ gs.toMove, which means p.color = gs.toMove
      have hcolor' : p.color = gs.toMove := Classical.not_not.mp hcolor
      -- hmem : m ∈ (pieceTargets gs sq p).filter (respectsPin pins) |>.filter (basicLegalAndSafe gs)
      have hmem_filter2 := List.mem_filter.mp hmem
      have hmem_filter1 := List.mem_filter.mp hmem_filter2.1
      exact ⟨p, heq, hcolor', hmem_filter1.1, hmem_filter1.2, hmem_filter2.2⟩

/--
Converts allLegalMoves membership to the encodedLegal structure.
The proof traces membership through the foldr structure of allLegalMoves.
-/
theorem mem_allLegalMoves_implies_encodedLegal (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    ∃ sq p,
      gs.board sq = some p ∧
      p.color = gs.toMove ∧
      m ∈ pieceTargets gs sq p ∧
      respectsPin (pinnedSquares gs gs.toMove) m = true ∧
      basicLegalAndSafe gs m = true := by
  intro hmem
  unfold allLegalMoves at hmem
  have h := Parsing.mem_foldr_append
    (fun sq => legalMovesForCached gs sq (pinnedSquares gs gs.toMove))
    [] allSquares m hmem
  rcases h with hinit | ⟨sq, _, hsq⟩
  · simp at hinit
  · have ⟨p, hBoard, hColor, hTargets, hPin, hSafe⟩ :=
      mem_legalMovesForCached_implies_encodedLegal gs sq _ m hsq
    exact ⟨sq, p, hBoard, hColor, hTargets, hPin, hSafe⟩

/--
Soundness lemma: Every move in allLegalMoves respects the geometry constraints.
This follows from pieceTargets generating moves that respect piece movement rules.

The proof proceeds by:
1. Converting allLegalMoves membership to the encodedLegal structure (via axiom)
2. Extracting the pieceTargets membership from encodedLegal
3. Applying respectsGeometry_of_pieceTargets (axiom) to conclude
-/
theorem allLegalMoves_sound_respectsGeometry (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    respectsGeometry gs m := by
  intro hMem
  -- Convert membership to encodedLegal structure
  have hEnc := mem_allLegalMoves_implies_encodedLegal gs m hMem
  rcases hEnc with ⟨sq, p, _hBoard, _hColor, hTargets, _hPin, _hSafe⟩
  -- Apply the axiom that pieceTargets respects geometry
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
  -- allLegalMoves only produces moves that pass basicLegalAndSafe
  -- basicLegalAndSafe requires basicMoveLegalBool = true
  -- basicMoveLegalBool includes both destinationFriendlyFree and captureFlagConsistent
  have hSafe : basicLegalAndSafe gs m = true :=
    Parsing.mem_allLegalMoves_implies_basicLegalAndSafe gs m hMem
  unfold basicLegalAndSafe at hSafe
  simp only [Bool.and_eq_true] at hSafe
  -- hSafe.1 : basicMoveLegalBool gs m = true
  -- hSafe.2 : kingSafeAfterMove gs m = true
  have hBasic := hSafe.1
  -- Unfold basicMoveLegalBool to get the individual conditions
  -- basicMoveLegalBool = originHasPiece && turnMatches && destinationFriendlyFree && captureFlagConsistent && squaresDiffer
  unfold basicMoveLegalBool at hBasic
  simp only [Bool.and_eq_true] at hBasic
  -- Destructure: hBasic has form ((((a, b), c), d), e)
  obtain ⟨⟨⟨⟨_hOrigin, _hTurn⟩, hDestFree⟩, hCapFlag⟩, _hDiff⟩ := hBasic
  -- hDestFree : destinationFriendlyFree gs m = true (which is destinationFriendlyFreeProp)
  -- hCapFlag : captureFlagConsistent gs m = true
  -- Apply the lemma from SemanticCaptureFlagLemmas
  exact captureFlagConsistentWithEP_of_destinationFriendlyFree_and_captureFlagConsistent gs m hDestFree hCapFlag

end Rules
end Chess
