import Chess.Analysis.MinimaxSpec

namespace Chess
namespace Analysis

open Rules

/-!
Alpha-beta (negamax form).

Note: this implementation is intentionally structured for later pruning proofs.
-/

def alphaBetaValue : Nat → GameState → Int → Int → Int
  | depth, gs, α, β =>
      match terminalValue? gs with
      | some v => v
      | none =>
          match depth with
          | 0 => staticEval gs
          | Nat.succ d =>
              alphaBetaList d gs (allLegalMoves gs) α β

where
  alphaBetaList : Nat → GameState → List Move → Int → Int → Int
    | _d, _gs, [], α, _β => α
    | d, gs, m :: ms, α, β =>
        let child := GameState.playMove gs m
        let score := -(alphaBetaValue d child (-β) (-α))
        let α' := if score > α then score else α
        if _h : α' ≥ β then
          α'
        else
          alphaBetaList d gs ms α' β

def alphaBeta (depth : Nat) (gs : GameState) : Int :=
  alphaBetaValue depth gs (-mateScore - 1) (mateScore + 1)

end Analysis
end Chess
