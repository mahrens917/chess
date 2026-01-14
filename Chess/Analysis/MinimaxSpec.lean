import Chess.Analysis.Spec

namespace Chess
namespace Analysis

open Rules

/--
A deterministic depth-limited minimax (negamax) value specification.

This intentionally mirrors the baseline `negamaxPV` value policy:
- terminal nodes use `terminalValue?`
- depth `0` uses `staticEval`
- otherwise we take the first strict maximum over `allLegalMoves`, with default `-mateScore - 1`.
-/
def minimaxValue : Nat → GameState → Int
  | depth, gs =>
      match terminalValue? gs with
      | some v => v
      | none =>
          match depth with
          | 0 => staticEval gs
          | Nat.succ d =>
              let moves := allLegalMoves gs
              let worst : Int := -mateScore - 1
              moves.foldl
                (fun best m =>
                  let child := GameState.playMove gs m
                  let score := -(minimaxValue d child)
                  if score > best then score else best)
                worst

end Analysis
end Chess

