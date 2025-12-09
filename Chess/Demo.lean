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

def demoStart : GameState := buildStartingState
def demoStartFen : String := toFEN demoStart

def demoScholarsPGN : String :=
  "[Event \"Scholars\"]\n\n1. e4 e5 2. Qh5 Nc6 3. Bc4 Nf6 4. Qxf7#"

def demoAfterE4 : Except String GameState := applySAN demoStart "e4"
def demoAfterScholars : Except String GameState := playPGN demoScholarsPGN

def demoFenRoundTrip : Except String String := do
  let parsed ← parseFEN demoStartFen
  pure (toFEN parsed)

def demoSanSamples : Except String (List String) := do
  let gs ← demoAfterE4
  let moves := gs.legalMoves.take 5
  pure (moves.map (moveToSAN gs))

def demoPgnSummary : Except String (String × Bool × Option String) := do
  let parsed ← playPGNStructured demoScholarsPGN
  pure (toFEN parsed.finalState, isCheckmate parsed.finalState, parsed.result)

def demoPerftDepths : List Nat := [1, 2, 3]

def startFromTagsIO (tags : List (String × String)) : IO GameState := do
  match startFromTags tags with
  | .ok gs => pure gs
  | .error e => throw <| IO.userError s!"Failed to seed PGN start: {e}"

def streamPgnMoves (game : PGNGame) : IO Unit := do
  let start ← startFromTagsIO game.tags
  let rec loop (ply : Nat) (gs : GameState) (remaining : List PGNMove) : IO GameState := do
    match remaining with
    | [] => pure gs
    | entry :: rest =>
        let moveNumber := ply / 2 + 1
        let prefixStr := if gs.toMove = Color.White then s!"{moveNumber}. " else s!"{moveNumber}... "
        let san := moveToSAN gs entry.move
        let nagSuffix := if entry.nags.isEmpty then "" else " {" ++ String.intercalate " " entry.nags ++ "}"
        IO.println s!"[Move] {prefixStr}{san}{nagSuffix}"
        match applyLegalMove gs entry.move with
        | .ok next => loop (ply + 1) next rest
        | .error err =>
            IO.eprintln s!"Failed to replay PGN move {prefixStr}{san}: {err}"
            pure gs
  let _ ← loop 0 start game.moves
  pure ()

structure DemoArgs where
  fen : Option String := none
  fenFile : Option System.FilePath := none
  pgnFile : Option System.FilePath := none
  perftDepth : Option Nat := none
  allowSlowPerft : Bool := false
  exportFen : Option System.FilePath := none
  exportSan : Option System.FilePath := none
  exportPgn : Option System.FilePath := none
  streamMoves : Bool := false
  showHelp : Bool := false
deriving Inhabited

def demoUsage : String :=
  String.intercalate "\n"
    [ "chessDemo usage:"
    , "  --fen \"<fen-string>\"        Parse and summarize a FEN string"
    , "  --fen-file <path>            Parse FEN loaded from a file"
    , "  --pgn-file <path>            Play a PGN file and print the final summary"
    , "  --perft <depth>              Run perft from the current base position (FEN if supplied)"
    , "  --allow-slow-perft          Allow perft depth ≥ 5 (prints nodes/second in the report)"
    , "  --export-fen <path>          Write the resulting state's FEN to a file"
    , "  --export-san <path>          Write newline-separated legal SAN moves for the final state"
    , "  --export-pgn <path>          Write PGN (source or stub) for the analyzed game"
    , "  --stream-moves               Print SAN commentary while replaying PGN input"
    , "If no flags are provided, the demo prints the built-in FEN/SAN/PGN/perft samples."
    ]

partial def parseDemoArgsAux (cfg : DemoArgs) : List String → Except String DemoArgs
  | [] => pure cfg
  | "--fen" :: fen :: rest =>
      if cfg.fen.isSome ∨ cfg.fenFile.isSome then
        throw "Multiple FEN inputs provided"
      else
        parseDemoArgsAux { cfg with fen := some fen } rest
  | "--fen" :: [] => throw "Missing argument for --fen"
  | "--fen-file" :: path :: rest =>
      if cfg.fen.isSome ∨ cfg.fenFile.isSome then
        throw "Multiple FEN inputs provided"
      else
        parseDemoArgsAux { cfg with fenFile := some <| System.FilePath.mk path } rest
  | "--fen-file" :: [] => throw "Missing argument for --fen-file"
  | "--pgn-file" :: path :: rest =>
      if cfg.pgnFile.isSome then
        throw "Multiple PGN files provided"
      else
        parseDemoArgsAux { cfg with pgnFile := some <| System.FilePath.mk path } rest
  | "--pgn-file" :: [] => throw "Missing argument for --pgn-file"
  | "--perft" :: depth :: rest =>
      match depth.toNat? with
      | some d => parseDemoArgsAux { cfg with perftDepth := some d } rest
      | none => throw s!"Invalid perft depth: {depth}"
  | "--perft" :: [] => throw "Missing argument for --perft"
  | "--export-fen" :: path :: rest =>
      match cfg.exportFen with
      | some _ => throw "Export FEN output already specified"
      | none => parseDemoArgsAux { cfg with exportFen := some <| System.FilePath.mk path } rest
  | "--export-fen" :: [] => throw "Missing argument for --export-fen"
  | "--export-san" :: path :: rest =>
      match cfg.exportSan with
      | some _ => throw "Export SAN output already specified"
      | none => parseDemoArgsAux { cfg with exportSan := some <| System.FilePath.mk path } rest
  | "--export-san" :: [] => throw "Missing argument for --export-san"
  | "--export-pgn" :: path :: rest =>
      match cfg.exportPgn with
      | some _ => throw "Export PGN output already specified"
      | none => parseDemoArgsAux { cfg with exportPgn := some <| System.FilePath.mk path } rest
  | "--export-pgn" :: [] => throw "Missing argument for --export-pgn"
  | "--stream-moves" :: rest =>
      parseDemoArgsAux { cfg with streamMoves := true } rest
  | "--allow-slow-perft" :: rest =>
      parseDemoArgsAux { cfg with allowSlowPerft := true } rest
  | "--help" :: _ => parseDemoArgsAux { cfg with showHelp := true } []
  | flag :: _ => throw s!"Unknown flag {flag}"

def parseDemoArgs (args : List String) : Except String DemoArgs :=
  parseDemoArgsAux {} args

def summaryFromState (label : String) (gs : GameState) : String :=
  let colorName : Color → String
    | Color.White => "white"
    | Color.Black => "black"
  let checkStatus :=
    if isCheckmate gs then "checkmate"
    else if isStalemate gs then "stalemate"
    else if inCheck gs.board gs.toMove then "check"
    else "ongoing"
  s!"[{label}] toMove={colorName gs.toMove}, status={checkStatus}, FEN={toFEN gs}, result={gs.result.getD "*"}"

def runFenInput (label fen : String) : IO GameState := do
  match parseFEN fen with
  | .ok gs =>
      IO.println (summaryFromState label gs)
      pure gs
  | .error e => throw <| IO.userError s!"Failed to parse FEN ({label}): {e}"

def runPgnFile (streamMoves : Bool) (path : System.FilePath) : IO (Option (PGNGame × String)) := do
  let contents ← IO.FS.readFile path
  match playPGNStructured contents with
  | .ok parsed =>
      IO.println s!"[PGN] tags={parsed.tags.length} moves={parsed.moves.length}"
      IO.println (summaryFromState "PGN final" parsed.finalState)
      if streamMoves then streamPgnMoves parsed else pure ()
      pure <| some (parsed, contents)
  | .error e => throw <| IO.userError s!"Failed to play PGN ({path}): {e}"

def perftSlowThreshold : Nat := 4

def ensurePerftAllowed (depth : Nat) (allowSlow : Bool) : IO Unit := do
  if depth > perftSlowThreshold ∧ ¬allowSlow then
    throw <| IO.userError s!"Perft depth {depth} requires --allow-slow-perft (threshold is {perftSlowThreshold})"

def runPerftReport (label : String) (gs : GameState) (depth : Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let nodes := perft gs depth
  let finish ← IO.monoNanosNow
  let elapsedNs := finish - start
  let elapsedMs := elapsedNs / 1000000
  let nodesPerSecond :=
    if elapsedNs = 0 then
      "inf"
    else
      let rate := (nodes * 1000000000) / elapsedNs
      toString rate
  IO.println s!"[Perft] {label} depth {depth} = {nodes} nodes in {elapsedMs}ms ({nodesPerSecond} nodes/s)"

def runDefaultDemo : IO Unit := do
  IO.println "[Demo] default summaries"
  IO.println s!"Start FEN: {demoStartFen}"
  IO.println s!"Start legal moves: {demoStart.legalMoves.length}"
  match demoFenRoundTrip with
  | .ok fen => IO.println s!"FEN round-trip succeeded: {fen}"
  | .error e => IO.println s!"FEN round-trip failed: {e}"
  match demoAfterE4 with
  | .ok gs => IO.println s!"After e4: {toFEN gs}"
  | .error e => IO.println s!"After e4 failed: {e}"
  match demoAfterScholars with
  | .ok gs =>
      IO.println s!"Scholars mate FEN: {toFEN gs}"
      IO.println s!"Checkmate? {isCheckmate gs}"
  | .error e => IO.println s!"Scholars mate failed: {e}"
  match demoSanSamples with
  | .ok sans => IO.println s!"Sample SAN list: {String.intercalate ", " sans}"
  | .error e => IO.println s!"SAN sample generation failed: {e}"
  match demoPgnSummary with
  | .ok (fen, mate, result) =>
      IO.println s!"PGN summary FEN: {fen}"
      IO.println s!"PGN mate flag: {mate}"
      IO.println s!"PGN recorded result: {result.getD "*"}"
  | .error e => IO.println s!"PGN summary failed: {e}"
  let samples := demoPerftDepths.map (fun d => (d, perft buildStartingState d))
  IO.println s!"Perft samples: {samples}"

def main (args : List String) : IO UInt32 := do
  let cfg ←
    match parseDemoArgs args with
    | .ok c => pure c
    | .error msg => do
        IO.eprintln msg
        IO.eprintln demoUsage
        throw <| IO.userError "Invalid arguments"
  if cfg.showHelp then
    IO.println demoUsage
    return 0
  let fenSource ←
    match cfg.fen, cfg.fenFile with
    | some fen, none => pure (some ("--fen", fen))
    | none, some path =>
        let contents ← IO.FS.readFile path
        pure (some ("--fen-file", contents.trim))
    | none, none => pure none
    | _, _ => pure none
  let fenState? ←
    match fenSource with
    | some (label, fen) => runFenInput label fen |>.map some
    | none => pure none
  let pgnInfo? ←
    match cfg.pgnFile with
    | some path => runPgnFile cfg.streamMoves path
    | none => pure none
  match cfg.perftDepth with
  | some depth =>
      let base := fenState?.getD buildStartingState
      ensurePerftAllowed depth cfg.allowSlowPerft
      runPerftReport "custom" base depth
  | none =>
      unless fenState?.isSome ∨ cfg.pgnFile.isSome do
        runDefaultDemo
  let finalState :=
    match pgnInfo? with
    | some (game, _) => game.finalState
    | none => fenState?.getD buildStartingState
  let targets : ExportTargets :=
    { fen := cfg.exportFen
      san := cfg.exportSan
      pgn := cfg.exportPgn }
  exportOutputs targets finalState (pgnInfo?.map (·.2))
  return 0
