import Chess.StateInvariants
import Chess.SemanticFideLegalEquivalence

namespace Chess
namespace Rules

theorem fideLegalSemantic_iff_mem_allLegalMoves_of_reachable (gs : GameState) (m : Move) :
    reachableFromStandard gs →
    (fideLegalSemantic gs m ↔ m ∈ allLegalMoves gs) := by
  intro hReach
  have hValid : hasValidEPRank gs := reachableFromStandard_hasValidEPRank gs hReach
  exact fideLegalSemantic_iff_mem_allLegalMoves gs m hValid

theorem fideLegalSemantic_iff_fideLegal_of_reachable (gs : GameState) (m : Move) :
    reachableFromStandard gs →
    (fideLegalSemantic gs m ↔ fideLegal gs m) := by
  intro hReach
  have hValid : hasValidEPRank gs := reachableFromStandard_hasValidEPRank gs hReach
  exact fideLegalSemantic_iff_fideLegal gs m hValid

end Rules
end Chess

