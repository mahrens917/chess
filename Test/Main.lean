import Chess.Core
import Chess.Movement
import Chess.Game

open Chess
open Movement
open Game

def check (desc : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"Test failed: {desc}"

def expectNat (desc : String) (actual expected : Nat) : IO Unit :=
  check desc (actual == expected)

def expectStr (desc actual expected : String) : IO Unit :=
  check desc (actual == expected)

def expectBool (desc : String) (actual expected : Bool) : IO Unit :=
  check desc (actual == expected)

def expectPieceOption (desc : String) (actual expected : Option Piece) : IO Unit :=
  check desc (actual == expected)

def expectColor (desc : String) (actual expected : Color) : IO Unit :=
  check desc (actual == expected)

def expectInt (desc : String) (actual expected : Int) : IO Unit :=
  check desc (actual == expected)

def kingCenter : Square := Square.mkUnsafe 4 4
def knightCorner : Square := Square.mkUnsafe 0 0
def knightCenter : Square := Square.mkUnsafe 4 4

def testTargetCounts : IO Unit := do
  expectNat "king targets from center" (kingTargets kingCenter |>.length) 8
  expectNat "knight targets from corner" (knightTargets knightCorner |>.length) 2
  expectNat "knight targets from center" (knightTargets knightCenter |>.length) 8
  expectNat "board square count" allSquares.length 64
  expectStr "algebraic a1" (Square.mkUnsafe 0 0).algebraic "a1"
  expectStr "algebraic h8" (Square.mkUnsafe 7 7).algebraic "h8"
  expectInt "pawn direction white" (pawnDirection Color.White) 1
  expectInt "pawn direction black" (pawnDirection Color.Black) (-1)

def sampleWhitePawn : Piece := { pieceType := PieceType.Pawn, color := Color.White }
def sampleBlackPawn : Piece := { pieceType := PieceType.Pawn, color := Color.Black }
def sampleBlackKing : Piece := { pieceType := PieceType.King, color := Color.Black }

def originSquare : Square := Square.mkUnsafe 4 1
def captureSquare : Square := Square.mkUnsafe 4 3
def otherSquare : Square := Square.mkUnsafe 7 7

def sampleBoard : Board :=
  emptyBoard
    |>.update originSquare (some sampleWhitePawn)
    |>.update captureSquare (some sampleBlackPawn)
    |>.update otherSquare (some sampleBlackKing)

def sampleMove : Move :=
  { piece := sampleWhitePawn
    fromSq := originSquare
    toSq := captureSquare
    isCapture := true
    promotion := none }

def initialState : GameState :=
  { board := sampleBoard, toMove := Color.White, halfMoveClock := 5, fullMoveNumber := 1 }

def runMoveTests : IO Unit := do
  let after := initialState.movePiece sampleMove
  expectPieceOption "source cleared after move" (after.board originSquare) none
  expectPieceOption "destination receives pawn" (after.board captureSquare) (some sampleWhitePawn)
  expectPieceOption "unrelated square preserved" (after.board otherSquare) (some sampleBlackKing)
  expectColor "turn flips" after.toMove Color.Black
  expectNat "half-move clock reset on capture" after.halfMoveClock 0
  expectNat "full-move number stays when white moves" after.fullMoveNumber 1

def main : IO UInt32 := do
  testTargetCounts
  runMoveTests
  IO.println s!"Chess tests completed successfully"
  pure 0
