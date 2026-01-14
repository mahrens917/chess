import Chess.Spec
import Chess.SemanticFideLegalSoundness
import Chess.SemanticPinFilterLemmas

namespace Chess
namespace Rules

theorem fideLegalSemantic_iff_mem_allLegalMoves (gs : GameState) (m : Move) :
    hasValidEPRank gs →
    (fideLegalSemantic gs m ↔ m ∈ allLegalMoves gs) := by
  intro hValid
  constructor
  · intro hSem
    exact fideLegalSemantic_implies_mem_allLegalMoves gs m hValid hSem
  · intro hMem
    exact allLegalMoves_sound_fideLegalSemantic gs m hValid hMem

theorem fideLegalSemantic_iff_fideLegal (gs : GameState) (m : Move) :
    hasValidEPRank gs →
    (fideLegalSemantic gs m ↔ fideLegal gs m) := by
  intro hValid
  have h1 : fideLegalSemantic gs m ↔ m ∈ allLegalMoves gs :=
    fideLegalSemantic_iff_mem_allLegalMoves gs m hValid
  have h2 : m ∈ allLegalMoves gs ↔ fideLegal gs m := by
    simpa using (allLegalMoves_iff_fideLegal gs m)
  exact h1.trans h2

end Rules
end Chess
