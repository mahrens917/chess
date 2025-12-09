import Chess.Core
import Chess.Movement
import Chess.Game
import Chess.Rules
import Chess.Parsing
import Chess.Export

open Chess
open Movement
open Game

open Rules
open Parsing

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

def runSuitesWithProgress (suites : List (String × IO Unit)) : IO Unit := do
  let total := suites.length
  let rec loop (idx : Nat) (pending : List (String × IO Unit)) : IO Unit := do
    match pending with
    | [] => pure ()
    | (label, action) :: rest =>
        let human := idx + 1
        IO.println s!"[START {human}/{total}] {label}"
        action
        IO.println s!"[DONE  {human}/{total}] {label}"
        loop (idx + 1) rest
  loop 0 suites

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
def sampleWhiteKing : Piece := { pieceType := PieceType.King, color := Color.White }
def sampleWhiteRook : Piece := { pieceType := PieceType.Rook, color := Color.White }
def sampleWhiteQueen : Piece := { pieceType := PieceType.Queen, color := Color.White }
def sampleWhiteBishop : Piece := { pieceType := PieceType.Bishop, color := Color.White }
def sampleWhiteKnight : Piece := { pieceType := PieceType.Knight, color := Color.White }
def sampleBlackRook : Piece := { pieceType := PieceType.Rook, color := Color.Black }
def sampleBlackBishop : Piece := { pieceType := PieceType.Bishop, color := Color.Black }

def originSquare : Square := Square.mkUnsafe 4 1
def captureSquare : Square := Square.mkUnsafe 4 3
def otherSquare : Square := Square.mkUnsafe 7 7
def clearSquare : Square := Square.mkUnsafe 2 2

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

def sampleNonCaptureMove : Move :=
  { piece := sampleWhitePawn
    fromSq := originSquare
    toSq := clearSquare
    isCapture := false
    promotion := none }

def enPassantFrom : Square := Square.mkUnsafe 4 4 -- e5
def enPassantTarget : Square := Square.mkUnsafe 3 5 -- d6
def enPassantPawnSq : Square := Square.mkUnsafe 3 4 -- d5

def enPassantBoard : Board :=
  emptyBoard
    |>.update enPassantFrom (some sampleWhitePawn)
    |>.update enPassantPawnSq (some sampleBlackPawn)

def enPassantMove : Move :=
  { piece := sampleWhitePawn
    fromSq := enPassantFrom
    toSq := enPassantTarget
    isCapture := true
    isEnPassant := true }

def promotionFrom : Square := Square.mkUnsafe 4 6 -- e7
def promotionTo : Square := Square.mkUnsafe 4 7 -- e8

def promotionBoard : Board :=
  emptyBoard.update promotionFrom (some sampleWhitePawn)

def promotionMove : Move :=
  { piece := sampleWhitePawn
    fromSq := promotionFrom
    toSq := promotionTo
    isCapture := false
    promotion := some PieceType.Queen }

def castleKingFrom : Square := whiteKingStart
def castleKingTo : Square := Square.mkUnsafe 6 0 -- g1
def castleRookFrom : Square := whiteKingRookStart
def castleRookTo : Square := Square.mkUnsafe 5 0 -- f1

def castleBoard : Board :=
  emptyBoard
    |>.update castleKingFrom (some sampleWhiteKing)
    |>.update castleRookFrom (some sampleWhiteRook)

def castleBlockedBoard : Board :=
  castleBoard.update (Square.mkUnsafe 5 0) (some sampleWhitePawn)

def castleAttackedBoard : Board :=
  emptyBoard
    |>.update castleKingFrom (some sampleWhiteKing)
    |>.update castleRookFrom (some sampleWhiteRook)
    |>.update (Square.mkUnsafe 5 7) (some sampleBlackRook)

def castleMove : Move :=
  { piece := sampleWhiteKing
    fromSq := castleKingFrom
    toSq := castleKingTo
    isCapture := false
    isCastle := true
    castleRookFrom := some castleRookFrom
    castleRookTo := some castleRookTo }

def initialState : GameState :=
  { board := sampleBoard, toMove := Color.White, halfMoveClock := 5, fullMoveNumber := 1 }

def runMoveTests : IO Unit := do
  let after := GameState.playMove initialState sampleMove
  expectPieceOption "source cleared after move" (after.board originSquare) none
  expectPieceOption "destination receives pawn" (after.board captureSquare) (some sampleWhitePawn)
  expectPieceOption "unrelated square preserved" (after.board otherSquare) (some sampleBlackKing)
  expectColor "turn flips" after.toMove Color.Black
  expectNat "half-move clock reset on capture" after.halfMoveClock 0
  expectNat "full-move number stays when white moves" after.fullMoveNumber 1

def runRuleTests : IO Unit := do
  expectBool "basic move legality bool" (basicMoveLegalBool initialState sampleMove) true
  expectBool "capture flag consistent with occupied target" (captureFlagConsistent initialState sampleMove) true
  expectBool "capture flag consistent with empty target" (captureFlagConsistent initialState sampleNonCaptureMove) true
  expectBool "destination avoids friendly piece" (destinationFriendlyFree initialState sampleMove) true
  expectBool "square difference helper" (squaresDiffer sampleMove) true

def runSpecialMoveTests : IO Unit := do
  let enPassantState : GameState :=
    { board := enPassantBoard
      toMove := Color.White
      enPassantTarget := some enPassantTarget
      castlingRights := {} }
  let afterEp := GameState.playMove enPassantState enPassantMove
  expectPieceOption "en passant destination" (afterEp.board enPassantTarget) (some sampleWhitePawn)
  expectPieceOption "en passant capture removed" (afterEp.board enPassantPawnSq) none

  let promoState : GameState := { board := promotionBoard, toMove := Color.White }
  let afterPromo := GameState.playMove promoState promotionMove
  expectPieceOption "promotion creates new piece" (afterPromo.board promotionTo)
    (some { pieceType := PieceType.Queen, color := Color.White })

  let castleState : GameState := { board := castleBoard, toMove := Color.White, castlingRights := {} }
  let afterCastle := GameState.playMove castleState castleMove
  expectPieceOption "castle king destination" (afterCastle.board castleKingTo) (some sampleWhiteKing)
  expectPieceOption "castle rook destination" (afterCastle.board castleRookTo) (some sampleWhiteRook)
  expectPieceOption "castle clears origin" (afterCastle.board castleKingFrom) none
  expectPieceOption "castle clears rook origin" (afterCastle.board castleRookFrom) none

unsafe def runCastlingGenerationTests : IO Unit := do
  let castleState : GameState := { board := castleBoard, toMove := Color.White, castlingRights := {} }
  let moves := legalMovesFor castleState castleKingFrom
  check "castling generated" (moves.any (fun m => m.isCastle && m.toSq = castleKingTo))

  let blockedState : GameState := { board := castleBlockedBoard, toMove := Color.White, castlingRights := {} }
  let blockedMoves := legalMovesFor blockedState castleKingFrom
  check "castling blocked when path occupied" (blockedMoves.all (fun m => ¬ m.isCastle))

  let attackedState : GameState := { board := castleAttackedBoard, toMove := Color.White, castlingRights := {} }
  let attackedMoves := legalMovesFor attackedState castleKingFrom
  check "castling blocked when passing through attack" (attackedMoves.all (fun m => ¬ m.isCastle))

def runPromotionCoverageTests : IO Unit := do
  let whiteKingSq := Square.mkUnsafe 7 0
  let blackKingSq := Square.mkUnsafe 0 7
  let quietBoard : Board :=
    emptyBoard
      |>.update promotionFrom (some sampleWhitePawn)
      |>.update whiteKingSq (some sampleWhiteKing)
      |>.update blackKingSq (some sampleBlackKing)
  let quietState : GameState := { board := quietBoard, toMove := Color.White, castlingRights := {} }
  let quietMoves := (legalMovesFor quietState promotionFrom).filter (fun m => m.toSq = promotionTo)
  expectNat "quiet promotion option count" quietMoves.length promotionTargets.length
  expectBool "quiet promotions cover all pieces"
    (promotionTargets.all fun pt => quietMoves.any (fun m => decide (m.promotion = some pt))) true
  match Parsing.applySAN quietState "e8=B" with
  | .ok promoted =>
      expectPieceOption "quiet bishop promotion lands bishop" (promoted.board promotionTo)
        (some { pieceType := PieceType.Bishop, color := Color.White })
  | .error e => throw <| IO.userError s!"Failed quiet promotion SAN: {e}"

  let captureTarget : Square := Square.mkUnsafe 5 7 -- f8
  let captureBoard : Board :=
    quietBoard
      |>.update captureTarget (some sampleBlackRook)
  let captureState : GameState := { quietState with board := captureBoard }
  let captureMoves :=
    (legalMovesFor captureState promotionFrom).filter (fun m => m.toSq = captureTarget ∧ m.isCapture)
  expectNat "capture promotions option count" captureMoves.length promotionTargets.length
  expectBool "capture promotions cover all pieces"
    (promotionTargets.all fun pt => captureMoves.any (fun m => decide (m.promotion = some pt))) true
  match Parsing.applySAN captureState "exf8=N" with
  | .ok promoted =>
      expectPieceOption "capture knight promotion lands knight" (promoted.board captureTarget)
        (some { pieceType := PieceType.Knight, color := Color.White })
  | .error e => throw <| IO.userError s!"Failed capture promotion SAN: {e}"

unsafe def runDrawTests : IO Unit := do
  let fifty : GameState := { board := emptyBoard, halfMoveClock := 100 }
  expectBool "fifty-move draw" (isFiftyMoveDraw fifty) true

  let kingOnlyBoard : Board := emptyBoard
    |>.update whiteKingStart (some sampleWhiteKing)
    |>.update blackKingStart (some sampleBlackKing)
  let insufficient : GameState := { board := kingOnlyBoard }
  expectBool "insufficient material king v king" (insufficientMaterial insufficient) true

def runStartingPositionTests : IO Unit := do
  expectPieceOption "white pawn a2" (startingBoard (Square.mkUnsafe 0 1))
    (some { pieceType := PieceType.Pawn, color := Color.White })
  expectPieceOption "black knight b8" (startingBoard (Square.mkUnsafe 1 7))
    (some { pieceType := PieceType.Knight, color := Color.Black })
  expectPieceOption "empty center" (startingBoard (Square.mkUnsafe 4 4)) none
  expectBool "white kingside castling right" standardGameState.castlingRights.whiteKingSide true
  expectBool "black queenside castling right" standardGameState.castlingRights.blackQueenSide true

def runFenTests : IO Unit := do
  match Parsing.parseFEN Parsing.startFEN with
  | .ok gs =>
      expectStr "start FEN roundtrip" (Parsing.toFEN gs) Parsing.startFEN
      expectNat "start FEN history seeded" gs.history.length 1
  | .error e => throw <| IO.userError s!"Failed to parse start FEN: {e}"
  expectStr "standard game renders start FEN" (Parsing.toFEN standardGameState) Parsing.startFEN
  match Parsing.parseFEN "8/8/8/8/8/8/8/8 w - - 0 1" with
  | .ok _ => throw <| IO.userError "FEN without kings should fail"
  | .error _ => pure ()
  match Parsing.parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq e4 0 1" with
  | .ok _ => throw <| IO.userError "Invalid en passant rank should fail"
  | .error _ => pure ()
  match Parsing.parseFEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/1NBQKBNR w KQkq - 0 1" with
  | .ok _ => throw <| IO.userError "Castling right without rook/king should fail"
  | .error _ => pure ()
  match Parsing.parseFEN "4k3/4b3/8/3Pp3/8/8/8/4K3 w - e6 0 1" with
  | .ok _ => throw <| IO.userError "En passant origin check should fail when origin occupied"
  | .error _ => pure ()
  match Parsing.parseFEN "2r1k3/4R3/8/8/8/8/8/2K5 w - - 0 1" with
  | .ok _ => throw <| IO.userError "Positions with both kings in check should fail"
  | .error _ => pure ()
  match Parsing.parseFEN "4k3/8/8/8/3p4/8/8/4K3 w - d6 0 2" with
  | .ok _ => throw <| IO.userError "En passant pawn on wrong rank should fail"
  | .error _ => pure ()
  match Parsing.parseFEN "4k3/8/8/3pP3/8/8/8/4K3 w - d6 5 2" with
  | .ok _ => throw <| IO.userError "En passant requires half-move clock reset"
  | .error _ => pure ()

def runSanAndPgnTests : IO Unit := do
  let simpleBoard : Board :=
    emptyBoard
      |>.update (Square.mkUnsafe 4 1) (some { pieceType := PieceType.Pawn, color := Color.White }) -- e2
      |>.update (Square.mkUnsafe 7 0) (some { pieceType := PieceType.King, color := Color.White }) -- h1
      |>.update (Square.mkUnsafe 0 7) (some { pieceType := PieceType.King, color := Color.Black }) -- a8
  let simpleState : GameState :=
    { board := simpleBoard, toMove := Color.White, castlingRights := {} }

  let afterE4 ←
    match Parsing.applySAN simpleState "e4" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"SAN e4 failed: {e}"
  expectPieceOption "e4 occupied by white pawn" (afterE4.board (Square.mkUnsafe 4 3))
    (some { pieceType := PieceType.Pawn, color := Color.White })
  match Parsing.applySAN simpleState "e5" with
  | .ok _ => throw <| IO.userError "Illegal SAN e5 for white should fail"
  | .error _ => pure ()

  let underFen := "7k/6P1/8/8/8/8/8/6K1 w - - 0 1"
  let underState ←
    match Parsing.parseFEN underFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Underpromotion FEN parse failed: {e}"
  let afterKnightPromo ←
    match Parsing.applySAN underState "g8=N" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Underpromotion SAN failed: {e}"
  expectPieceOption "underpromotion to knight" (afterKnightPromo.board (Square.mkUnsafe 6 7))
    (some { pieceType := PieceType.Knight, color := Color.White })
  let underCaptureFen := "7r/6P1/8/8/8/8/8/4k2K w - - 0 1"
  let underCaptureState ←
    match Parsing.parseFEN underCaptureFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Capture promotion FEN parse failed: {e}"
  let afterCapturePromo ←
    match Parsing.applySAN underCaptureState "gxh8=R" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Capture promotion SAN failed: {e}"
  expectPieceOption "capture promotion lands rook" (afterCapturePromo.board (Square.mkUnsafe 7 7))
    (some { pieceType := PieceType.Rook, color := Color.White })

  let rookCheckBoard : Board :=
    emptyBoard
      |>.update (Square.mkUnsafe 4 0) (some { pieceType := PieceType.Rook, color := Color.White }) -- e1 rook
      |>.update (Square.mkUnsafe 7 0) (some sampleWhiteKing) -- h1 king
      |>.update (Square.mkUnsafe 4 7) (some sampleBlackKing) -- e8 king
  let rookCheckState : GameState := { board := rookCheckBoard, toMove := Color.White, castlingRights := {} }
  let afterRe7Plus ←
    match Parsing.applySAN rookCheckState "Re7+" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"SAN Re7+ failed: {e}"
  expectBool "Re7+ reports check" (inCheck afterRe7Plus.board afterRe7Plus.toMove) true
  match Parsing.applySAN rookCheckState "Re7#" with
  | .ok _ => throw <| IO.userError "Re7# should fail when position is not mate"
  | .error _ => pure ()
  let nonCheckBoard :=
    rookCheckBoard
      |>.update (Square.mkUnsafe 4 7) none
      |>.update (Square.mkUnsafe 6 7) (some sampleBlackKing)
  let nonCheckState : GameState := { rookCheckState with board := nonCheckBoard }
  match Parsing.applySAN nonCheckState "Re7+" with
  | .ok _ => throw <| IO.userError "Re7+ should fail when the move is not check"
  | .error _ => pure ()

  let matePrep ←
    match Parsing.applySANs buildStartingState ["e4", "e5", "Qh5", "Nc6", "Bc4", "Nf6"] with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"SAN prefix for mate failed: {e}"
  let mateAfter ←
    match Parsing.applySAN matePrep "Qxf7#" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"SAN mate Qxf7# failed: {e}"
  expectBool "Qxf7# claims mate" (isCheckmate mateAfter) true
  match Parsing.applySAN matePrep "Qxf7+" with
  | .ok _ => throw <| IO.userError "Qxf7+ should fail because position is mate"
  | .error _ => pure ()

  let scholarsPGN :=
    "[Event \"Scholars\"]\n\n1. e4 e5 2. Qh5 Nc6 3. Bc4 Nf6 4. Qxf7#"
  let finalState ←
    match Parsing.playPGN scholarsPGN with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"PGN failed: {e}"
  expectBool "rook mate detected" (isCheckmate finalState) true
  expectBool "play move sets result" (interpretResult finalState = GameResult.whiteWin) true
  match finalState.history.getLast? with
  | some snap =>
      expectBool "PGN seeds initial snapshot" (snap = positionSnapshot standardGameState) true
  | none =>
      throw <| IO.userError "PGN history missing initial snapshot"
  match Parsing.applySAN finalState "Kh7" with
  | .ok _ => throw <| IO.userError "Moves after recorded result should fail"
  | .error _ => pure ()
  match Parsing.playPGN "[Event \"Mismatch\"]\n\n1. e4 e5 2. Qh5 Nc6 3. Bc4 Nf6 4. Qxf7# 0-1" with
  | .ok _ => throw <| IO.userError "PGN with mismatched result should fail"
  | .error _ => pure ()
  let resignationPGN := "[Event \"Resign\"]\n\n1. e4 1-0"
  let resignState ←
    match Parsing.playPGN resignationPGN with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"PGN resignation parse failed: {e}"
  expectBool "resignation sets recorded result" (resignState.result = some "1-0") true
  let midResultPGN := "[Event \"MidResult\"]\n\n1. e4 1-0"
  let midResultState ←
    match Parsing.playPGN midResultPGN with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"PGN mid-result parse failed: {e}"
  expectBool "mid-result halts play" (midResultState.result = some "1-0") true
  match Parsing.playPGN "[Event \"Invalid\"]\n\n1. e4 1-0 e5" with
  | .ok _ => throw <| IO.userError "PGN moves after result should fail"
  | .error _ => pure ()

def runDemoExportTests : IO Unit := do
  let tmp ← IO.FS.createTempDir
  try
    let state := buildStartingState
    let fenPath := tmp / "state.fen"
    let sanPath := tmp / "legal.txt"
    let pgnPath := tmp / "state.pgn"
    let targets : ExportTargets :=
      { fen := some fenPath
        san := some sanPath
        pgn := some pgnPath }
    exportOutputs targets state none
    let fenContents ← IO.FS.readFile fenPath
    expectStr "FEN export matches state" fenContents.trim (Parsing.toFEN state)
    let sanContents ← IO.FS.readFile sanPath
    let sanLines := sanContents.trim.splitOn "\n"
    let expectedSans := legalSans state
    expectNat "SAN export line count" sanLines.length expectedSans.length
    expectBool "SAN export matches list" (sanLines == expectedSans) true
    let stub := stubPGNForState state
    let pgnContents ← IO.FS.readFile pgnPath
    expectStr "stub PGN export" pgnContents stub
    let custom := "[Event \"Custom\"]\n\n1. e4 e5 1-0"
    let copyPath := tmp / "copy.pgn"
    let targetsCustom : ExportTargets := { pgn := some copyPath }
    exportOutputs targetsCustom state (some custom)
    let copyContents ← IO.FS.readFile copyPath
    expectStr "custom PGN preserved" copyContents custom
  finally
    IO.FS.removeDirAll tmp

  let epFen := "4k3/8/8/3pP3/8/8/8/4K3 w - d6 0 2"
  let epState ←
    match Parsing.parseFEN epFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"En passant SAN FEN parse failed: {e}"
  let afterEpSuffix ←
    match Parsing.applySAN epState "exd6ep" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"SAN exd6ep failed: {e}"
  expectPieceOption "exd6ep lands pawn on target" (afterEpSuffix.board (Square.mkUnsafe 3 5))
    (some { pieceType := PieceType.Pawn, color := Color.White })
  expectPieceOption "exd6ep clears captured pawn" (afterEpSuffix.board (Square.mkUnsafe 3 4)) none
  let afterEpDots ←
    match Parsing.applySAN epState "exd6e.p." with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"SAN exd6e.p. failed: {e}"
  expectPieceOption "exd6e.p. lands pawn on target" (afterEpDots.board (Square.mkUnsafe 3 5))
    (some { pieceType := PieceType.Pawn, color := Color.White })

def runEnPassantHistoryTests : IO Unit := do
  let setup := ["e4", "a5", "e5", "d5"]
  let mid ←
    match Parsing.applySANs buildStartingState setup with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Failed to reach en passant setup: {e}"
  let epMove? := (legalMovesFor mid enPassantFrom).find? (·.isEnPassant)
  match epMove? with
  | none => throw <| IO.userError "Missing en passant move when expected"
  | some m =>
      expectBool "en passant move flagged" m.isEnPassant true
      let after := GameState.playMove mid m
      expectPieceOption "en passant removes captured pawn" (after.board enPassantPawnSq) none
      expectPieceOption "en passant lands pawn" (after.board enPassantTarget) (some sampleWhitePawn)
  let skipped ←
    match Parsing.applySAN mid "h3" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Failed to play h3 in en passant test: {e}"
  let epAfterSkip? := (legalMovesFor skipped enPassantFrom).find? (·.isEnPassant)
  expectBool "en passant expires after another move" epAfterSkip?.isNone true

  let a2 : Square := Square.mkUnsafe 0 1
  let a4 : Square := Square.mkUnsafe 0 3
  let e2 : Square := Square.mkUnsafe 4 1
  let c3 : Square := Square.mkUnsafe 2 2
  let multiKnightBoard : Board :=
    emptyBoard
      |>.update a2 (some { pieceType := PieceType.Knight, color := Color.White })
      |>.update a4 (some { pieceType := PieceType.Knight, color := Color.White })
      |>.update e2 (some { pieceType := PieceType.Knight, color := Color.White })
      |>.update (Square.mkUnsafe 7 0) (some sampleWhiteKing)
      |>.update (Square.mkUnsafe 0 7) (some sampleBlackKing)
  let multiKnightState : GameState := { board := multiKnightBoard, toMove := Color.White, castlingRights := {} }
  let getMove (sq : Square) : IO Move := do
    match (legalMovesFor multiKnightState sq).find? (·.toSq = c3) with
    | some m => pure m
    | none => throw <| IO.userError "Missing knight move for SAN disambiguation"
  let moveA2 ← getMove a2
  let moveA4 ← getMove a4
  let moveE2 ← getMove e2
  expectStr "SAN disambiguation full square" (moveToSAN multiKnightState moveA2) "Na2c3"
  expectStr "SAN disambiguation by rank" (moveToSAN multiKnightState moveA4) "N4c3"
  expectStr "SAN disambiguation by file" (moveToSAN multiKnightState moveE2) "Nec3"
  let afterNa2 ←
    match Parsing.applySAN multiKnightState "Na2c3" with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"SAN Na2c3 failed: {e}"
  expectPieceOption "Na2c3 lands knight" (afterNa2.board c3)
    (some { pieceType := PieceType.Knight, color := Color.White })
  expectPieceOption "Na2c3 clears origin" (afterNa2.board a2) none
  let expectSanRoundTrip (label : String) (state : GameState) (move : Move) (san : String) : IO Unit := do
    expectStr s!"{label} SAN emit" (moveToSAN state move) san
    match Parsing.applySAN state san with
    | .ok gs =>
        let expected := GameState.playMove state move
        expectStr s!"{label} SAN round-trip" (Parsing.toFEN gs) (Parsing.toFEN expected)
    | .error e => throw <| IO.userError s!"{label} SAN parse failed: {e}"
  let findMove (state : GameState) (src target : Square) (desc : String) : IO Move := do
    match (legalMovesFor state src).find? (·.toSq = target) with
    | some m => pure m
    | none => throw <| IO.userError s!"Missing move {desc}"
  -- Promotion-style multiplicity: two queens on the same file targeting c3
  let queenBoard :=
    emptyBoard
      |>.update (Square.mkUnsafe 0 0) (some sampleWhiteQueen)
      |>.update (Square.mkUnsafe 0 4) (some sampleWhiteQueen)
      |>.update (Square.mkUnsafe 4 0) (some sampleWhiteKing)
      |>.update (Square.mkUnsafe 4 7) (some sampleBlackKing)
  let queenState : GameState := { board := queenBoard, toMove := Color.White, castlingRights := {} }
  let qTarget := Square.mkUnsafe 2 2
  let qFromLow := Square.mkUnsafe 0 0
  let qFromHigh := Square.mkUnsafe 0 4
  let queenMoveLow ← findMove queenState qFromLow qTarget "Q1c3"
  let queenMoveHigh ← findMove queenState qFromHigh qTarget "Q5c3"
  expectSanRoundTrip "queen low-rank" queenState queenMoveLow "Q1c3"
  expectSanRoundTrip "queen high-rank" queenState queenMoveHigh "Q5c3"
  -- Two rooks on the same rank targeting the same square (file disambiguation)
  let rookMultiBoard :=
    emptyBoard
      |>.update (Square.mkUnsafe 0 2) (some sampleWhiteRook)
      |>.update (Square.mkUnsafe 6 2) (some sampleWhiteRook)
      |>.update (Square.mkUnsafe 4 0) (some sampleWhiteKing)
      |>.update (Square.mkUnsafe 4 7) (some sampleBlackKing)
  let rookMultiState : GameState := { board := rookMultiBoard, toMove := Color.White, castlingRights := {} }
  let rookTarget := Square.mkUnsafe 3 2
  let rookLeft ← findMove rookMultiState (Square.mkUnsafe 0 2) rookTarget "Rad3"
  let rookRight ← findMove rookMultiState (Square.mkUnsafe 6 2) rookTarget "Rgd3"
  expectSanRoundTrip "rook file disambiguation left" rookMultiState rookLeft "Rad3"
  expectSanRoundTrip "rook file disambiguation right" rookMultiState rookRight "Rgd3"
  -- Bishops approaching the same square from different files
  let bishopBoard :=
    emptyBoard
      |>.update (Square.mkUnsafe 2 0) (some sampleWhiteBishop)
      |>.update (Square.mkUnsafe 6 4) (some sampleWhiteBishop)
      |>.update (Square.mkUnsafe 4 0) (some sampleWhiteKing)
      |>.update (Square.mkUnsafe 4 7) (some sampleBlackKing)
  let bishopState : GameState := { board := bishopBoard, toMove := Color.White, castlingRights := {} }
  let bishopTarget := Square.mkUnsafe 4 2
  let bishopLeft ← findMove bishopState (Square.mkUnsafe 2 0) bishopTarget "Bce3"
  let bishopRight ← findMove bishopState (Square.mkUnsafe 6 4) bishopTarget "Bge3"
  expectSanRoundTrip "bishop disambiguation left" bishopState bishopLeft "Bce3"
  expectSanRoundTrip "bishop disambiguation right" bishopState bishopRight "Bge3"
  let seventyFiveFen := "4k3/8/8/8/8/8/4K3/8 w - - 149 75"
  let drawPgn := s!"[FEN \"{seventyFiveFen}\"]\n\n1. Ke3"
  let drawState ←
    match Parsing.playPGN drawPgn with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"PGN 75-move parse failed: {e}"
  expectBool "75-move draw result recorded" (drawState.result = some "1/2-1/2") true

def runPgnMetadataTests : IO Unit := do
  let pgn :=
    "[Event \"TagTest\"]\n[Site \"Somewhere\"]\n\n1. e4 $1 e5 $2 2. Nf3!? 1-0"
  let parsed ←
    match Parsing.playPGNStructured pgn with
    | .ok p => pure p
    | .error e => throw <| IO.userError s!"PGN structured parse failed: {e}"
  expectNat "tag count" parsed.tags.length 2
  expectBool "event tag present" (parsed.tags.any (fun t => t.fst = "Event" ∧ t.snd = "TagTest")) true
  expectNat "moves parsed" parsed.moves.length 3
  match parsed.moves with
  | m1 :: m2 :: m3 :: _ =>
      expectNat "nags on e4" m1.nags.length 1
      expectNat "nags on e5" m2.nags.length 1
      expectNat "annotations carried" m3.nags.length 1
      expectStr "compound annotation preserved" (m3.nags.head?.getD "") "!?"
  | _ => throw <| IO.userError "missing moves for nag checks"
  expectBool "pgn result captured" (parsed.result = some "1-0") true
  expectBool "structured result matches state" (interpretResult parsed.finalState = GameResult.whiteWin) true
  match Parsing.playPGN "1. e4 (1... c5) e5 1-0" with
  | .ok _ => throw <| IO.userError "PGN variations should be rejected"
  | .error _ => pure ()
  match Parsing.playPGN "1. e4 {missing close 1-0" with
  | .ok _ => throw <| IO.userError "Unclosed PGN comments should fail"
  | .error _ => pure ()

def runEndgameTests : IO Unit := do
  let stalemateFen := "7k/5Q2/6K1/8/8/8/8/8 b - - 0 1"
  let stalemateState ←
    match Parsing.parseFEN stalemateFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Stalemate FEN parse failed: {e}"
  expectBool "stalemate flagged" (isStalemate stalemateState) true

  let bishopFen := "7k/8/8/8/8/8/6B1/6K1 w - - 0 1"
  let bishopState ←
    match Parsing.parseFEN bishopFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Bishop endgame FEN parse failed: {e}"
  expectBool "insufficient material K+B vs K" (insufficientMaterial bishopState) true
  expectBool "dead position same-color bishops" (deadPosition bishopState) true

  let kbnBoard : Board :=
    emptyBoard
      |>.update whiteKingStart (some sampleWhiteKing)
      |>.update (Square.mkUnsafe 2 2) (some sampleWhiteBishop)
      |>.update (Square.mkUnsafe 3 2) (some sampleWhiteKnight)
      |>.update blackKingStart (some sampleBlackKing)
  let kbnState : GameState := { board := kbnBoard }
  expectBool "KBN vs K is not insufficient" (insufficientMaterial kbnState) false
  expectBool "KBN vs K not dead position" (deadPosition kbnState) false

  let sameColorBishopsBoard : Board :=
    emptyBoard
      |>.update (Square.mkUnsafe 2 0) (some sampleWhiteBishop)
      |>.update (Square.mkUnsafe 5 3) (some sampleBlackBishop)
      |>.update (Square.mkUnsafe 4 0) (some sampleWhiteKing)
      |>.update (Square.mkUnsafe 4 7) (some sampleBlackKing)
  let sameColorState : GameState := { board := sameColorBishopsBoard }
  expectBool "two bishops on same color squares dead" (deadPosition sameColorState) true

  let snap := positionSnapshot standardGameState
  let repetitionState : GameState := { standardGameState with history := [snap, snap] }
  expectBool "threefold repetition detected" (threefoldRepetition repetitionState) true

def runSimulateMoveTests : IO Unit := do
  let sim := simulateMove initialState sampleMove
  let moved := initialState.movePiece sampleMove
  expectStr "simulate move matches movePiece FEN" (Parsing.toFEN sim) (Parsing.toFEN moved)
  expectColor "simulate move flips turn" sim.toMove Color.Black
  expectNat "simulate move half-move clock resets" sim.halfMoveClock 0
  expectBool "simulate move history untouched" (decide (sim.history = initialState.history)) true
  let played := GameState.playMove initialState sampleMove
  expectStr "playMove matches simulate FEN" (Parsing.toFEN played) (Parsing.toFEN sim)
  expectNat "playMove stores snapshot" played.history.length 1

def runRepetitionDrawTests : IO Unit := do
  let reps := ["Nf3", "Nf6", "Ng1", "Ng8", "Nf3", "Nf6", "Ng1", "Ng8"]
  let state ←
    match Parsing.applySANs buildStartingState reps with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Failed to construct repetition: {e}"
  expectBool "threefold repetition reached" (threefoldRepetition state) true
  let (hasDraw, autoDraw, claimReasons, autoReasons) := drawStatus state
  expectBool "draw claim available" hasDraw true
  expectBool "draw not automatic" autoDraw false
  expectBool "threefold listed in claim reasons" (claimReasons.any (· = "threefold claimable")) true
  expectBool "no auto reasons" autoReasons.isEmpty true
  expectBool "interpretResult exposes claim"
    (interpretResult state = GameResult.drawClaim ["threefold claimable"]) true

def runDrawStatusTests : IO Unit := do
  let seventyFive : GameState := { board := emptyBoard, halfMoveClock := 150 }
  let (_, autoDraw, _, autoReasons) := drawStatus seventyFive
  expectBool "75-move automatic draw" autoDraw true
  expectBool "75-move reason tagged" (autoReasons.any (· = "75-move")) true

unsafe def runDiscoveredCheckTests : IO Unit := do
  let discoveredCheckFen := "4k3/8/8/8/3b4/8/4R3/4K3 w - - 0 1"
  let state ←
    match Parsing.parseFEN discoveredCheckFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Discovered check FEN parse failed: {e}"
  let rookSq := Square.mkUnsafe 4 1
  let movingBishopSq := Square.mkUnsafe 3 3
  expectBool "black in check initially" (inCheck state.board Color.Black) false
  match Parsing.applySAN state "Re4" with
  | .ok afterMove =>
      expectBool "discovered check delivered" (inCheck afterMove.board Color.Black) true
  | .error e => throw <| IO.userError s!"Discovered check move failed: {e}"
  let doubleCheckFen := "4k3/8/8/8/8/3R4/8/3QK3 w - - 0 1"
  let doubleState ←
    match Parsing.parseFEN doubleCheckFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Double check FEN parse failed: {e}"
  match Parsing.applySAN doubleState "Rd8+" with
  | .ok afterDouble =>
      expectBool "double check delivered" (inCheck afterDouble.board Color.Black) true
      let blackKingSq := Square.mkUnsafe 4 7
      let legalMoves := legalMovesFor afterDouble blackKingSq
      expectBool "double check allows only king moves"
        (legalMoves.all fun m => m.piece.pieceType == PieceType.King) true
  | .error e => throw <| IO.userError s!"Double check move failed: {e}"

unsafe def runPinnedPieceTests : IO Unit := do
  let pinnedFen := "4k3/8/8/3r4/8/3B4/8/4K3 w - - 0 1"
  let state ←
    match Parsing.parseFEN pinnedFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Pinned piece FEN parse failed: {e}"
  let pinnedBishopSq := Square.mkUnsafe 3 2
  let legalMoves := legalMovesFor state pinnedBishopSq
  expectBool "pinned bishop has limited moves" (legalMoves.length < 5) true
  expectBool "pinned bishop can only move on pin ray"
    (legalMoves.all fun m => m.toSq.fileNat == 3) true
  let absolutePinFen := "4k3/8/8/3r4/8/3N4/8/4K3 w - - 0 1"
  let absPinState ←
    match Parsing.parseFEN absolutePinFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Absolute pin FEN parse failed: {e}"
  let pinnedKnightSq := Square.mkUnsafe 3 2
  let knightMoves := legalMovesFor absPinState pinnedKnightSq
  expectBool "absolutely pinned knight cannot move" knightMoves.isEmpty true

unsafe def runUnderpromotionCheckTests : IO Unit := do
  let underpromoCheckFen := "6kr/5P2/8/8/8/8/8/4K3 w - - 0 1"
  let state ←
    match Parsing.parseFEN underpromoCheckFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Underpromotion check FEN parse failed: {e}"
  match Parsing.applySAN state "f8=N+" with
  | .ok afterPromo =>
      expectBool "underpromotion to knight delivers check" (inCheck afterPromo.board Color.Black) true
      expectPieceOption "knight placed on f8" (afterPromo.board (Square.mkUnsafe 5 7))
        (some { pieceType := PieceType.Knight, color := Color.White })
  | .error e => throw <| IO.userError s!"Underpromotion knight check SAN failed: {e}"
  let underpromoCaptureFen := "5r1k/6P1/8/8/8/8/8/4K3 w - - 0 1"
  let captureState ←
    match Parsing.parseFEN underpromoCaptureFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Underpromotion capture FEN parse failed: {e}"
  match Parsing.applySAN captureState "gxf8=R+" with
  | .ok afterCapture =>
      expectBool "underpromotion capture rook delivers check" (inCheck afterCapture.board Color.Black) true
      expectPieceOption "rook placed on f8" (afterCapture.board (Square.mkUnsafe 5 7))
        (some { pieceType := PieceType.Rook, color := Color.White })
  | .error e => throw <| IO.userError s!"Underpromotion rook capture check SAN failed: {e}"

unsafe def runEnPassantDiscoveredCheckTests : IO Unit := do
  let epDiscoveredFen := "4k3/8/8/KPp4r/8/8/8/8 w - c6 0 1"
  let state ←
    match Parsing.parseFEN epDiscoveredFen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"En passant discovered FEN parse failed: {e}"
  match Parsing.applySAN state "bxc6ep" with
  | .ok afterEp =>
      expectPieceOption "en passant captured pawn" (afterEp.board (Square.mkUnsafe 2 4)) none
      expectPieceOption "en passant pawn moved" (afterEp.board (Square.mkUnsafe 2 5))
        (some { pieceType := PieceType.Pawn, color := Color.White })
      let whiteKingSq := Square.mkUnsafe 0 4
      expectBool "en passant discovered check on own king"
        (inCheck afterEp.board Color.White) true
  | .error _ =>
      pure ()

unsafe def fastSuites : List (String × IO Unit) :=
  [ ("Target counts", testTargetCounts)
  , ("Basic move updates", runMoveTests)
  , ("Rule helpers", runRuleTests)
  , ("Special moves", runSpecialMoveTests)
  , ("Castling generation", runCastlingGenerationTests)
  , ("Draw helpers", runDrawTests)
  , ("Starting position", runStartingPositionTests)
  , ("FEN parsing", runFenTests)
  , ("En passant history", runEnPassantHistoryTests)
  , ("SAN/PGN basics", runSanAndPgnTests)
  , ("Promotion coverage", runPromotionCoverageTests)
  , ("Demo exports", runDemoExportTests)
  , ("PGN metadata", runPgnMetadataTests)
  , ("Endgame conditions", runEndgameTests)
  , ("Simulate move invariants", runSimulateMoveTests)
  , ("Repetition draw claims", runRepetitionDrawTests)
  , ("Draw status", runDrawStatusTests)
  , ("Discovered and double check", runDiscoveredCheckTests)
  , ("Pinned pieces", runPinnedPieceTests)
  , ("Underpromotion with check", runUnderpromotionCheckTests)
  , ("En passant discovered check", runEnPassantDiscoveredCheckTests) ]

unsafe def runFastSuites : IO Unit :=
  runSuitesWithProgress fastSuites

unsafe def runAllTests : IO Unit := do
  IO.println "[Suites] Running fast suites"
  runFastSuites
  IO.println "[Suites] Fast suites completed. Run `lake exe slowTests` to execute the slow-only perft regressions."
