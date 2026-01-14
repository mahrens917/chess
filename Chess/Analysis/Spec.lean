import Chess.Rules

namespace Chess
namespace Analysis

open Rules

def mateScore : Int :=
  100000

def pieceValue : PieceType → Int
  | PieceType.Pawn => 100
  | PieceType.Knight => 320
  | PieceType.Bishop => 330
  | PieceType.Rook => 500
  | PieceType.Queen => 900
  | PieceType.King => 0

def materialScore (b : Board) : Int :=
  Square.all.foldl
    (fun acc sq =>
      match b sq with
      | none => acc
      | some p =>
          let v := pieceValue p.pieceType
          match p.color with
          | Color.White => acc + v
          | Color.Black => acc - v)
    0

/--
Static evaluation from the perspective of `gs.toMove`.
Positive means “good for the side to move”.
-/
def staticEval (gs : GameState) : Int :=
  let whiteScore := materialScore gs.board
  match gs.toMove with
  | Color.White => whiteScore
  | Color.Black => -whiteScore

def winnerColorScore (toMove winner : Color) : Int :=
  if toMove = winner then mateScore else -mateScore

/--
Terminal evaluation from the perspective of `gs.toMove`.

Policy choice: treat both auto-draw and claimable draw as value `0`.
-/
def terminalValue? (gs : GameState) : Option Int :=
  if isCheckmate gs then
    some (-mateScore)
  else
    match interpretResult gs with
    | GameResult.whiteWin => some (winnerColorScore gs.toMove Color.White)
    | GameResult.blackWin => some (winnerColorScore gs.toMove Color.Black)
    | GameResult.drawAuto _ => some 0
    | GameResult.drawClaim _ => some 0
    | GameResult.ongoing =>
        if isStalemate gs then
          some 0
        else
          none

end Analysis
end Chess

