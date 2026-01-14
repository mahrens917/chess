import Chess.Rules
import Chess.ParsingProofs

namespace Chess
namespace Rules

/-!
`Chess.RulesComplete` provides a *definitional* “rules-complete” spec for the
current executable move generator.

This is intentionally separate from the semantic (FIDE-like) legality predicate
`Chess.Rules.fideLegalSemantic`. The key deliverable here is a proved
equivalence between a Prop-level spec and `allLegalMoves` membership, so
downstream developments (parsers, search, etc.) can state correctness theorems
against a stable predicate rather than a list generator.
-/

/--
Prop-level legality predicate corresponding *exactly* to the executable move
generator `allLegalMoves`.

This is the “rules-complete” predicate for the current implementation.
-/
def encodedLegal (gs : GameState) (m : Move) : Prop :=
  ∃ sq p,
    gs.board sq = some p ∧
    p.color = gs.toMove ∧
    m ∈ pieceTargets gs sq p ∧
    respectsPin (pinnedSquares gs gs.toMove) m = true ∧
    basicLegalAndSafe gs m = true

theorem encodedLegal_of_mem_legalMovesForCached
    (gs : GameState) (sq : Square) (pins : List (Square × Square)) (m : Move) :
    m ∈ legalMovesForCached gs sq pins →
    ∃ p,
      gs.board sq = some p ∧
      p.color = gs.toMove ∧
      m ∈ pieceTargets gs sq p ∧
      respectsPin pins m = true ∧
      basicLegalAndSafe gs m = true := by
  intro hMem
  unfold legalMovesForCached at hMem
  cases hBoard : gs.board sq with
  | none =>
      have : False := by
        simp [hBoard] at hMem
      cases this
  | some p =>
      by_cases hTurn : p.color ≠ gs.toMove
      ·
        have : False := by
          simp [hBoard, hTurn] at hMem
        cases this
      · -- Membership survived both filters.
        have hMem' :
            m ∈
              List.filter (fun cand => basicLegalAndSafe gs cand)
                ((pieceTargets gs sq p).filter (fun cand => respectsPin pins cand)) := by
          simpa [hBoard, hTurn] using hMem
        -- Unpack filter membership.
        have hMem0 :
            m ∈ (pieceTargets gs sq p).filter (fun cand => respectsPin pins cand) ∧
              basicLegalAndSafe gs m = true := by
          simpa [List.mem_filter] using (List.mem_filter.1 hMem')
        have hMemTargets :
            m ∈ pieceTargets gs sq p ∧ respectsPin pins m = true := by
          simpa [List.mem_filter] using (List.mem_filter.1 hMem0.1)
        have hColor : p.color = gs.toMove := by
          by_cases hEq : p.color = gs.toMove
          · exact hEq
          · exfalso
            exact hTurn hEq
        refine ⟨p, rfl, hColor, hMemTargets.1, hMemTargets.2, hMem0.2⟩

theorem mem_allLegalMoves_iff_encodedLegal (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs ↔ encodedLegal gs m := by
  constructor
  · intro hMem
    -- Recover the generating square and cached legality filter.
    unfold allLegalMoves at hMem
    let pins := pinnedSquares gs gs.toMove
    have hFold :
        m ∈ (Square.all).foldr (fun sq acc => legalMovesForCached gs sq pins ++ acc) [] := by
      simpa [allSquares, pins] using hMem
    have hExists :=
      (Chess.Parsing.List.mem_foldr_append_iff (f := fun sq => legalMovesForCached gs sq pins) (b := m) Square.all).1
        hFold
    rcases hExists with ⟨sq, _hSqMem, hInCached⟩
    have hEnc := encodedLegal_of_mem_legalMovesForCached gs sq pins m hInCached
    rcases hEnc with ⟨p, hBoard, hColor, hTargets, hPin, hSafe⟩
    refine ⟨sq, p, hBoard, hColor, hTargets, ?_, hSafe⟩
    -- Re-index the pin condition to match the cached pins value.
    simpa [pins] using hPin
  · intro hEnc
    -- Show membership by choosing the witness square from `encodedLegal`.
    rcases hEnc with ⟨sq, p, hBoard, hColor, hTargets, hPin, hSafe⟩
    unfold allLegalMoves
    let pins := pinnedSquares gs gs.toMove
    have hSqMem : sq ∈ (Square.all : List Square) := Square.mem_all sq
    have hInCached : m ∈ legalMovesForCached gs sq pins := by
      unfold legalMovesForCached
      by_cases hTurn : p.color ≠ gs.toMove
      · cases (hTurn hColor)
      · -- Now membership is purely filter membership.
        have hPinMem : m ∈ (pieceTargets gs sq p).filter (fun cand => respectsPin pins cand) := by
          exact List.mem_filter.2 ⟨hTargets, by simpa [pins] using hPin⟩
        have hMem :
            m ∈
              List.filter (fun cand => basicLegalAndSafe gs cand)
                ((pieceTargets gs sq p).filter (fun cand => respectsPin pins cand)) := by
          exact List.mem_filter.2 ⟨hPinMem, hSafe⟩
        simpa [hBoard, hTurn] using hMem
    have hMemFold :
        m ∈ (Square.all).foldr (fun sq acc => legalMovesForCached gs sq pins ++ acc) [] := by
      exact (Chess.Parsing.List.mem_foldr_append_iff (f := fun sq => legalMovesForCached gs sq pins) (b := m) Square.all).2
        ⟨sq, hSqMem, hInCached⟩
    simpa [allSquares, pins] using hMemFold

end Rules
end Chess
