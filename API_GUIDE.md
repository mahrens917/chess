# Library API Guide

This repo is both an executable chess rules engine and a Lean proof development.
This page documents the stable “entry points” most users want.

## Imports

- Core data types: `import Chess.Core`
- Move generation + legality: `import Chess.Rules`
- Apply moves / simulate: `import Chess.Game`
- Notation + parsing: `import Chess.Parsing`
- PGN exports: `import Chess.Export`
- Proof umbrella (compiles the full proof surface): `import Chess.Proofs`

## Common Tasks

### Parse FEN → `GameState`

- Function: `Chess.Parsing.parseFEN : String → Except String GameState`
- Pretty-print: `Chess.Parsing.toFEN : GameState → String`
- Constant: `Chess.Parsing.startFEN : String`

### Generate legal moves

- All moves: `Chess.Rules.allLegalMoves : GameState → List Move`
- Moves from one square: `Chess.Rules.legalMovesFor : GameState → Square → List Move`

### Apply / preview a move

- Apply (updates history/clocks/rights/EP): `Chess.Game.GameState.playMove : GameState → Move → GameState`
- Preview (board/rights/EP, with history frozen): `Chess.Game.simulateMove : GameState → Move → GameState`

### Check / end conditions

- In check: `Chess.Rules.inCheck : Board → Color → Bool`
- Draw helpers: see `Chess.Rules` (`isFiftyMoveDraw`, `isSeventyFiveMoveDraw`, repetition helpers, etc.)

### SAN

- Move → SAN: `Chess.Parsing.moveToSAN : GameState → Move → String`
- SAN → `Move`: `Chess.Parsing.moveFromSAN : GameState → String → Except String Move`
- Apply a SAN token: `Chess.Parsing.applySAN : GameState → String → Except String GameState` (auto-seeds history if missing)
- Apply SAN tokens: `Chess.Parsing.applySANs : GameState → List String → Except String GameState` (auto-seeds history if missing)

### PGN

- Replay PGN: `Chess.Parsing.playPGN : String → Except String GameState`
- Structured parse/replay: `Chess.Parsing.playPGNStructured : String → Except String PGNGame`

## Specs and Proof Surfaces

- Rules-complete Prop spec (generator-exact): `Chess/RulesComplete.lean` (`encodedLegal`)
- Semantic (FIDE-like) legality predicate: `Chess/Spec.lean` (`fideLegalSemantic`)
- Proof index: `THEOREM_INDEX.md`
