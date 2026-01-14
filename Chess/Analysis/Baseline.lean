import Chess.Analysis.Spec

namespace Chess
namespace Analysis

open Rules

structure PVResult where
  value : Int
  pv : List Move
deriving Repr

def negamaxPV : Nat → GameState → PVResult
  | depth, gs =>
      match terminalValue? gs with
      | some v => { value := v, pv := [] }
      | none =>
          match depth with
          | 0 => { value := staticEval gs, pv := [] }
          | Nat.succ d =>
              let moves := allLegalMoves gs
              let worst : PVResult := { value := -mateScore - 1, pv := [] }
              moves.foldl
                (fun best m =>
                  let child := GameState.playMove gs m
                  let childRes := negamaxPV d child
                  let score := -childRes.value
                  if score > best.value then
                    { value := score, pv := m :: childRes.pv }
                  else
                    best)
                worst

def negamax (depth : Nat) (gs : GameState) : Int :=
  (negamaxPV depth gs).value

end Analysis
end Chess
