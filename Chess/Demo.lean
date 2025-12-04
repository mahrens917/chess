import Chess.Core
import Chess.Movement
import Chess.Game

open Chess
open Movement
open Game

def demoCenter : Square := Square.mkUnsafe 4 4
def demoPawn : Piece := { pieceType := PieceType.Pawn, color := Color.White }
def demoSource : Square := Square.mkUnsafe 4 1 -- e2
def demoDestination : Square := Square.mkUnsafe 4 3 -- e4
def demoMove : Move :=
  { piece := demoPawn, from := demoSource, to := demoDestination, isCapture := false }

def demoGame : GameState := GameState.default
def demoAfterMove : GameState := demoGame.movePiece demoMove

#eval demoCenter.algebraic
#eval kingTargets demoCenter |>.map Square.algebraic
#eval knightTargets demoCenter |>.map Square.algebraic
#eval demoAfterMove.toMove
#eval demoAfterMove.halfMoveClock
#eval demoAfterMove.fullMoveNumber
