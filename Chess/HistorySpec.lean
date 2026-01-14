import Chess.Rules

namespace Chess
namespace Rules

theorem finalizeResult_history (before after : GameState) :
    (finalizeResult before after).history = after.history := by
  unfold finalizeResult
  cases hRes : after.result.isSome <;>
    cases hMate : isCheckmate after <;>
    cases hDraw :
        (isStalemate after || isSeventyFiveMoveDraw after || fivefoldRepetition after ||
          insufficientMaterial after || deadPosition after) <;>
      simp [hRes, hMate, hDraw]

theorem GameState.playMove_history (gs : GameState) (m : Move) :
    (GameState.playMove gs m).history =
      gs.history ++ [positionSnapshot (gs.movePiece m)] := by
  unfold GameState.playMove
  simp [finalizeResult_history]

theorem threefoldRepetition_eq_count (gs : GameState) :
    threefoldRepetition gs =
      decide ((gs.history ++ [positionSnapshot gs]).count (positionSnapshot gs) ≥ 3) := by
  simp [threefoldRepetition]

theorem fivefoldRepetition_eq_count (gs : GameState) :
    fivefoldRepetition gs =
      decide ((gs.history ++ [positionSnapshot gs]).count (positionSnapshot gs) ≥ 5) := by
  simp [fivefoldRepetition]

end Rules
end Chess
