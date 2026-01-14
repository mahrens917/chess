import Chess.ParsingProofs
import Chess.Rules

namespace Chess
namespace Rules

theorem mem_allLegalMoves_nonCastle_rookFields_none (gs : GameState) (m : Move) :
    m ∈ allLegalMoves gs →
    ¬m.isCastle →
    m.castleRookFrom = none ∧ m.castleRookTo = none := by
  intro hMem hNotCastle
  have hCastleFalse : m.isCastle = false := by
    cases h : m.isCastle with
    | false => simpa using h
    | true => cases (hNotCastle h)
  exact Chess.Parsing.mem_allLegalMoves_implies_castleRook_none gs m hMem hCastleFalse

end Rules
end Chess

