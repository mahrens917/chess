import Chess.Core
import Chess.Game
import Chess.Rules
import Chess.Parsing

namespace Chess

open Rules
open Parsing

structure ExportTargets where
  fen : Option System.FilePath := none
  san : Option System.FilePath := none
  pgn : Option System.FilePath := none
deriving Inhabited

def legalSans (gs : GameState) : List String :=
  (GameState.legalMoves gs).map (moveToSAN gs)

def stubPGNForState (gs : GameState) : String :=
  let fen := toFEN gs
  let result := gs.result.getD "*"
  let tags :=
    [ ("Event", "chessDemo export")
    , ("Site", "CLI")
    , ("SetUp", "1")
    , ("FEN", fen)
    , ("Result", result) ]
  let tagBlock :=
    tags.map (fun (k, v) => s!"[{k} \"{v}\"]") |>
      String.intercalate "\n"
  tagBlock ++ "\n\n" ++ (if result = "*" then "*" else result)

def writeOptionalFile (path? : Option System.FilePath) (contents : String) : IO Unit := do
  match path? with
  | some path => IO.FS.writeFile path contents
  | none => pure ()

def exportOutputs (targets : ExportTargets) (finalState : GameState) (pgnSource? : Option String) : IO Unit := do
  writeOptionalFile targets.fen (toFEN finalState)
  writeOptionalFile targets.san (String.intercalate "\n" (legalSans finalState))
  let pgnText :=
    match pgnSource? with
    | some txt => txt
    | none => stubPGNForState finalState
  writeOptionalFile targets.pgn pgnText

end Chess
