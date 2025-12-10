# Chess: Lean 4 Formalization of Standard Chess Rules

This repository builds a Lean 4 model of the classic chess game: board geometry, pieces, movement predicates, and the core game state logic.

## Proof Status

**Build:** ✓ Clean | **Tests:** 14/14 Passing | **Formal Proofs:** 209 Complete, 10 In Progress

| Category | Status |
|----------|--------|
| Movement Invariants | ✓ Complete (6/6 proven) |
| Game State Preservation | ✓ Complete (8/8 proven) |
| Move Generation | ⚠ Nearly Complete (5/6 pieces proven, pawn blocked on 2 sorries) |
| Parser Soundness | ⚠ Partial (7/10 proven) |
| Perft Correctness | ⚠ Partial (1/6 proven) |
| Draw Detection | ✓ Complete (proven) |

**Detailed Status:** See [PROOF_STATUS.md](PROOF_STATUS.md) for live metrics and [PLAN.md](PLAN.md) for roadmap.

## Layout

- `Chess/Core.lean` defines files/ranks, squares, colors, pieces, boards, and the `GameState` structure.
- `Chess/Movement.lean` encodes each piece's legal moves and includes helper lemmas about those movements.
- `Chess/Game.lean` updates the board, tracks turns, and proves board-update invariants.
- `Chess/Demo.lean` exercises the board helpers via `#eval` expressions and powers a lightweight executable.

## Roadmap Highlights

- Core feature parity and rule coverage are tracked in `PLAN.md` (movement, parsing robustness, draw detection).
- Proof backlog (also in `PLAN.md`) drives Lean theorems for move generators, `GameState` invariants, perft correctness, and parser soundness.
- Before Phase 5, we will add a small program that computes and prints the estimated perfect-game search space (baseline `10^120, raw move-tree baseline, known`) and updates it with reductions (e.g., `10^110, piece symmetry reduction, known`) as proofs land; this program will be the single source of truth for search-space figures.

## Build

```bash
lake build
lake exe chessDemo
lake exe searchSpace
```

The `chessDemo` executable prints algebraic square names, king/knight targets, and move-state details defined in `Chess/Demo.lean`.

Command-line options:

```bash
lake exe chessDemo -- --fen "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
lake exe chessDemo -- --fen-file board.fen --perft 3
lake exe chessDemo -- --fen-file board.fen --perft 5 --allow-slow-perft
lake exe chessDemo -- --pgn-file game.pgn
lake exe chessDemo -- --pgn-file game.pgn --stream-moves
lake exe chessDemo -- --fen-file board.fen --export-fen out.fen --export-san legal.txt
lake exe chessDemo -- --pgn-file game.pgn --export-pgn copy.pgn
```

Use `lake exe chessDemo -- --help` to see every supported flag. Perft runs now emit elapsed milliseconds plus nodes-per-second; depths above 4 are guarded behind `--allow-slow-perft` so that heavy calculations only run when explicitly requested.

The `searchSpace` executable dumps the current list of perfect-game search-space estimates and reductions documented in `Chess/SearchSpace.lean`; update that file as new proofs land.

## Tests

Run the Lean test suite with:

```bash
lake test
```

Run the fast Lean test suite with:

```bash
lake test
```

Run the perft-heavy slow suite with:

```bash
lake exe slowTests
```

Each suite announces `[START x/y]` and `[DONE x/y]` markers so you can track progress. Keep `lake test` for day-to-day work and run `lake exe slowTests` when you need the deeper perft baselines (start depth 1–3 plus en-passant/castling depth 3), the dedicated depth-4 pawn endgame benchmark, the PGN corpus replay, or the FEN fuzz round-robin.

## Reference Specifications

- [FIDE Laws of Chess](https://handbook.fide.com/chapter/E012023) for movement, castling, draw, and repetition rules.
- [Portable Game Notation (PGN)](https://www.chessclub.com/user/help/PGN-spec) and [Standard Algebraic Notation (SAN)] for recording and parsing moves.
- [Forsyth–Edwards Notation (FEN)](https://www.chessprogramming.org/Forsyth-Edwards_Notation) for serializing positions.

All new rules or helpers must cite the relevant specification and link their Lean proofs to those references.

## Project Assumptions

- No clock management: time controls, adjournments, or sealed moves are ignored. Only the half-move/full-move counters stored in `GameState` influence draw detection.
- Only classical rules are modeled: no chess variants, no underpromotion restrictions, and no arbiter interventions beyond PGN-tagged results.
- Tablebases/fortress heuristics are out of scope; automatic draws are limited to stalemate, repetition, 50/75-move counters, insufficient material, and encoded dead-position heuristics.
- Perft, SAN, PGN, and CLI flows assume legal input; invalid data is rejected with descriptive `Except` errors rather than attempting recovery.

## Notation Cheat Sheet

- **FEN (Forsyth–Edwards Notation)** — a single-line snapshot of a chess position describing piece placement (rank-by-rank), side to move (`w`/`b`), castling availability (`KQkq` subset), en-passant target square, half-move clock, and full-move number. We use it to seed `GameState`s and serialize boards for fixtures or demos. Optional metadata tokens can follow the canonical six fields; `unmoved=KQkq` records which castling flags remain physically possible so the parser rejects impossible rights. When an en-passant target is present, the parser now fully reconstructs the implied double-push (origin square empty, intermediate square empty, pawn sitting on the correct file/start rank) and appends the pre-double-push snapshot to `GameState.history` so repetition accounting reflects the hidden move.
- **SAN (Standard Algebraic Notation)** — per-move algebraic strings such as `Qxe5+`, `O-O`, or `exd6ep` that encode the moving piece, captures, disambiguation hints, promotions, en-passant suffixes, and check/mate markers. SAN drives `Parsing.applySAN`/`moveToSAN`.
- **PGN (Portable Game Notation)** — text files combining SAN move lists with optional `[Tag "Value"]` metadata. PGNs can embed comments (`{...}`), numeric annotation glyphs (`$1`, `!?`), and final results (`1-0`, `0-1`, `1/2-1/2`, `*`). We parse PGNs into structured games, enforce legality, and ensure recorded results match the board.

## PGN/SAN Behavior

- SAN check/mate hints are validated against the resulting position; `Qxf7+` fails when the board shows mate, and vice versa for `#`.
- PGN comments within `{ ... }` and semicolon line comments are removed, but braces must balance—missing `}` is a parse error.
- PGN variations `( ... )` are not supported; they raise descriptive errors so callers sanitize inputs or split games deterministically.
- Numeric annotation glyphs (`$1`, `!`, `!?`, etc.) are attached to the preceding move to preserve metadata during parsing.
- SAN tokens accept en passant suffixes like `ep`, `e.p.`, or `e.p` appended directly to the move (e.g., `exd6ep`) and normalize them automatically.

## Usage Examples

- `#eval Parsing.toFEN standardGameState` — emit the canonical starting FEN.
- `#eval let gs := buildStartingState; Parsing.applySAN gs "e4"` — start from the canonical history-seeded opening position before replaying SAN.
- `#eval Parsing.playPGN demoScholarsPGN` — load a SAN move list, verify legality, and surface the recorded result.
- `#eval perft standardGameState 3` — count all legal move trees to depth 3 (run `lake exe slowTests` to exercise deeper baselines).

## Canonical FEN/SAN/PGN Workflow

Every test or demo that needs a custom position should rely on the shared helpers so repetition tracking, draw clocks, and history snapshots stay consistent.

1. **Seed the starting board** — call `buildStartingState` for the usual opening position or `Parsing.parseFEN` for arbitrary fixtures. Both paths run through `seedHistory`, so `GameState.history` always contains the initial snapshot used by repetition checks.
   ```lean
   def scholarsMate? : Except String GameState := do
     let start := buildStartingState
     Parsing.applySANs start ["e4", "e5", "Qh5", "Nc6", "Bc4", "Nf6", "Qxf7#"]
   ```
2. **Apply SAN reliably** — use `Parsing.applySAN`/`applySANs` inside tests to advance states instead of calling `movePiece` directly. These helpers parse the algebraic move, resolve ambiguity, and then dispatch to `GameState.playMove`, guaranteeing that half-move clocks, castling rights, and en-passant targets are finalized the same way the CLI does.
3. **Load PGNs through the parser** — prefer `Parsing.playPGN` (final board only) or `Parsing.playPGNStructured` (tags + move metadata). Tagged games automatically honor an embedded `[FEN "..."]` start position, allowing tests and demos to reuse the same PGN artefacts without manual board edits.
   ```lean
   def loadTaggedGame (pgn : String) : Except String (List (String × String) × GameState) := do
     let parsed ← Parsing.playPGNStructured pgn
     pure (parsed.tags, parsed.finalState)
   ```
4. **Round-trip fixtures** — serialize intermediate nodes with `Parsing.toFEN` (for debugging) or pass the resulting state to `Chess.Export.exportOutputs` so CLI flows (`lake exe chessDemo`) can dump synchronized FEN/SAN/PGN outputs.

`Test/Main.lean` and `Chess/Demo.lean` already follow this pattern; new contributors should mirror the same helpers so feature and proof coverage grows around a single code path.

## Formal Proofs

This section catalogs all theorems and lemmas that have been formally proven in Lean. Every new rule, parser, or helper must ultimately be justified by Lean theorems that state the intended invariant (legal move equivalence, draw conditions, parser soundness, etc.) and prove it from first principles.

### Movement Invariants

Located in `Chess/Movement.lean`:

- `theorem rook_move_straight` — Establishes that rook moves are always along a file or rank (one coordinate matches).
- `theorem knight_move_distance` — Proves the knight's L-shaped move has Manhattan distance exactly 3.
- `theorem king_step_bounds` — Guarantees king moves are at most one square in both file and rank.
- `theorem pawn_advance_direction` — Shows pawn advances move in the correct direction (1 or 2 squares forward).
- `theorem pawn_capture_offset` — Ensures pawn captures are exactly one file away.
- `theorem pawn_capture_forward` — Confirms pawn captures move forward by exactly one rank.

### Game State Preservation

Located in `Chess/Game.lean`:

The `simulateMove` function produces a preview state for check detection without modifying history. The following theorems prove that `simulateMove` preserves all game state fields except history:

- `@[simp] theorem simulateMove_board` — Board state matches `movePiece`.
- `@[simp] theorem simulateMove_toMove` — Active player matches `movePiece`.
- `@[simp] theorem simulateMove_halfMoveClock` — Half-move clock matches `movePiece`.
- `@[simp] theorem simulateMove_fullMoveNumber` — Full-move counter matches `movePiece`.
- `@[simp] theorem simulateMove_enPassantTarget` — En passant target matches `movePiece`.
- `@[simp] theorem simulateMove_castlingRights` — Castling rights match `movePiece`.
- `@[simp] theorem simulateMove_result` — Game result matches `movePiece`.
- `@[simp] theorem simulateMove_history` — History is frozen (unchanged from input).

### Result Finalization

Located in `Chess/Rules.lean`:

The `finalizeResult` function updates the game result after a move while preserving all other state. These theorems establish that finalization only touches the result field:

- `@[simp] theorem finalizeResult_board` — Board remains unchanged.
- `@[simp] theorem finalizeResult_toMove` — Active player remains unchanged.
- `@[simp] theorem finalizeResult_halfMoveClock` — Half-move clock remains unchanged.
- `@[simp] theorem finalizeResult_fullMoveNumber` — Full-move counter remains unchanged.
- `@[simp] theorem finalizeResult_enPassantTarget` — En passant target remains unchanged.
- `@[simp] theorem finalizeResult_castlingRights` — Castling rights remain unchanged.

### Move Application

Located in `Chess/Rules.lean`:

The `playMove` function combines `movePiece` with history updates and result finalization. These theorems prove it preserves board/clock state while potentially updating the result:

- `@[simp] theorem playMove_board` — Board state matches `simulateMove`.
- `@[simp] theorem playMove_toMove` — Active player matches `simulateMove`.
- `@[simp] theorem playMove_halfMoveClock` — Half-move clock matches `simulateMove`.
- `@[simp] theorem playMove_fullMoveNumber` — Full-move counter matches `simulateMove`.
- `@[simp] theorem playMove_enPassantTarget` — En passant target matches `simulateMove`.
- `@[simp] theorem playMove_castlingRights` — Castling rights match `simulateMove`.

### Parser Soundness and Completeness

Located in `Chess/Parsing.lean`:

This section establishes formal guarantees for FEN/SAN/PGN parsing and serialization. All theorems are currently admitted with `sorry` and require proof implementation.

**Helper Definitions:**
- `GameStateEquiv` — Equivalence relation for game states (same board position and metadata).
- `MoveEquiv` — Equivalence relation for moves (same board transformation).

**FEN Round-Trip Properties:**
- `theorem parseFEN_toFEN_roundtrip` — Parsing a generated FEN produces an equivalent position.
- `theorem toFEN_produces_valid_fen` — Every game state can be serialized to valid FEN.
- `theorem parseFEN_start_position` — Standard starting FEN parses to standard position.
- `theorem parsePlacement_requires_8_ranks` — FEN placement must have exactly 8 ranks.
- `theorem parsePlacement_rank_has_8_squares` — Each FEN rank must represent 8 squares.

**FEN Rejection Properties:**
- `theorem parseFEN_valid_kings` — Valid FENs must have exactly one king per side.
- `theorem parseFEN_rejects_no_white_king` — FENs without white king are rejected.
- `theorem parseFEN_rejects_adjacent_kings` — Adjacent kings are illegal.
- `theorem parseFEN_rejects_pawns_on_back_rank` — Pawns on rank 1 or 8 are illegal.
- `theorem parseFEN_rejects_too_many_pawns` — More than 8 pawns per side is illegal.
- `theorem parseFEN_rejects_ep_without_reset` — En passant requires half-move clock = 0.

**SAN Round-Trip Properties:**
- `theorem moveFromSAN_moveToSAN_roundtrip` — Parsing generated SAN produces equivalent move.
- `theorem moveFromSAN_preserves_move_structure` — SAN parsing preserves piece, squares, and turn.
- `theorem parseSanToken_normalizes_castling` — Castling notation with '0' is normalized to 'O'.
- `theorem moveFromSanToken_validates_check_hint` — Check/mate hints match resulting position.

**SAN Soundness (parsed moves are legal):**
- `theorem moveFromSAN_sound` — Every parsed SAN produces a legal move.
- `theorem moveFromSanToken_sound` — Parsed moves are in `allLegalMoves`.
- `theorem moveFromSanToken_matches_base` — Parsed move matches the SAN base representation.
- `theorem moveFromSAN_preserves_turn` — Parsed moves respect turn order.
- `theorem moveFromSAN_promotion_rank` — Promotions target the correct rank.

**SAN Completeness (all legal moves have SAN):**
- `theorem moveToSAN_complete` — Every legal move can be expressed as SAN.
- `theorem moveToSAN_unique` — SAN representation is unambiguous.
- `theorem sanDisambiguation_minimal` — Disambiguation uses minimal sufficient information.
- `theorem moveToSAN_castling_format` — Castling uses O-O or O-O-O format.
- `theorem moveToSAN_pawn_capture_includes_file` — Pawn captures include source file.

**PGN Parsing Properties:**
- `theorem stripPGNNoise_preserves_moves` — Comment removal preserves move tokens.
- `theorem playPGNStructured_preserves_sequence` — Move sequence is preserved.
- `theorem playPGNStructured_result_consistent` — Result tags match final state.
- `theorem playPGN_reachable` — Final state is reachable from start position.
- `theorem stripPGNNoise_rejects_unbalanced` — Unbalanced braces produce errors.

**Parser Composition Properties:**
- `theorem applySAN_equivalent_to_playPGN` — Single SAN application matches PGN parsing.
- `theorem applySANs_matches_playPGN` — Sequential SAN matches PGN parsing.

**Invariant Preservation:**
- `theorem parseFEN_preserves_invariants` — Parsed FENs maintain king requirements.
- `theorem moveFromSAN_rejects_invalid` — Invalid SAN produces errors.
- `theorem moveFromSAN_rejects_ambiguous` — Ambiguous SAN produces errors.

### Proof Backlog

The following critical invariants still require proof implementation (tracked in `PLAN.md`):

- **Move Generation Completeness** — Prove `allLegalMoves` generates exactly the set of legal moves according to FIDE rules.
- **Draw Detection Soundness** — Prove 50/75-move, threefold/fivefold repetition, insufficient material, and dead position detectors are correct.
- **Parser Soundness/Completeness** — Complete the proofs for the 35 parsing theorems declared above (currently admitted with `sorry`).
- **Perft Correctness** — Inductively prove `perft` counts match the theoretical move tree expansion.

### Proof Requirements for Contributors

When adding features or modifying existing rules:

1. **State the invariant** — Write a clear theorem statement expressing the intended property.
2. **Prove from first principles** — Use Lean's tactics to derive the result from existing definitions.
3. **Link to specifications** — Cite FIDE Laws, PGN spec, SAN spec, or FEN spec in comments.
4. **Document here** — Add the theorem to the appropriate section above once it lands.
5. **Mark simp where appropriate** — Use `@[simp]` for equational lemmas that simplify expressions.

The objective is not to solve chess outright, but to algorithmically shrink the solvable search space as far as possible, with each reduction accompanied by proofs that justify the pruning.

## Developer Guide

### Adding New Rules

When implementing new chess rules (movement, castling, draw detection, etc.):

1. **Implementation** — Add the rule logic to the appropriate module:
   - Movement predicates go in `Chess/Movement.lean`
   - Game state updates go in `Chess/Game.lean`
   - Rule checking goes in `Chess/Rules.lean`

2. **Required Proofs** — Every rule must include theorems that establish:
   - Correctness (the rule matches FIDE Laws of Chess)
   - Preservation of invariants (e.g., single occupancy, piece counts)
   - Consistency with existing rules (no contradictions)

3. **Required Tests** — Add executable tests to both suites:
   - Fast smoke tests in `Test/Main.lean` for basic validation
   - Comprehensive tests in `SlowTests/` for edge cases, perft validation, etc.

4. **Required Documentation** — Update:
   - This README's "Formal Proofs" section with new theorems
   - The "Reference Specifications" section with FIDE citations
   - `PLAN.md` to mark completed proof obligations
   - Code comments linking definitions to specification sections

5. **Validation Workflow**:
   ```bash
   lake build            # Ensure code and proofs type-check
   lake test             # Run fast test suite
   lake exe slowTests    # Run comprehensive slow tests
   ```

### Checklist for Extending SAN/FEN/PGN

When adding or modifying parsing/serialization functionality:

#### FEN (Forsyth-Edwards Notation)

- [ ] Update `Parsing.parseFEN` in `Chess/Parsing.lean` for new syntax
- [ ] Update `Parsing.toFEN` to emit the new format
- [ ] Add round-trip tests: `parseFEN (toFEN state) = state`
- [ ] Update the "Notation Cheat Sheet" section in this README
- [ ] Prove `parseFEN` soundness: parsed states satisfy board invariants
- [ ] Prove `toFEN` completeness: all valid states can be serialized
- [ ] Cite the FEN specification in code comments and PR description

#### SAN (Standard Algebraic Notation)

- [ ] Update `Parsing.applySAN` for new move syntax
- [ ] Update `Parsing.moveToSAN` to emit the new format
- [ ] Add round-trip tests: `applySAN (moveToSAN gs m) = m` (up to equivalence)
- [ ] Update the "Notation Cheat Sheet" section in this README
- [ ] Validate check/mate hints match actual board state
- [ ] Prove SAN disambiguation is unique and minimal
- [ ] Cite the SAN specification in code comments and PR description

#### PGN (Portable Game Notation)

- [ ] Update `Parsing.playPGN` or `Parsing.playPGNStructured` for new features
- [ ] Handle new tag types in `startFromTags`
- [ ] Update comment/variation/NAG handling if applicable
- [ ] Add corpus tests with real-world PGN files in `SlowTests/`
- [ ] Update the "PGN/SAN Behavior" section in this README
- [ ] Prove PGN result tags match computed game outcomes
- [ ] Cite the PGN specification in code comments and PR description

#### Shared Helpers

Always reuse these functions to maintain consistency:

- `buildStartingState` — Seeds history for standard opening position
- `Parsing.parseFEN` — Seeds history for arbitrary positions
- `Parsing.applySAN` / `applySANs` — Applies moves with full legality checking
- `Parsing.playPGN` / `playPGNStructured` — Loads complete games
- `Chess.Export.exportOutputs` — Writes FEN/SAN/PGN in synchronized format

### Adding Reductions to SearchSpace

The `searchSpace` executable (defined in `Chess/SearchSpace.lean`) reports perfect-game search-space estimates and reductions. To add a new reduction:

1. **Prove the Reduction** — Establish a Lean theorem or provide a formal citation justifying the pruning. Heuristic values are not acceptable.

2. **Update the Reduction List** — Add an entry to `Chess/SearchSpace.lean`:
   ```lean
   def myReduction : List Reduction :=
     [ { estimate := "10^110"
         label := "Piece symmetry reduction"
         status := "proven"  -- or "cited" with reference
         notes := "Link to theorem: Chess.Proofs.pieceSymmetryReduction" } ]
   ```

3. **Document Provenance** — In the `notes` field:
   - For proven reductions, link to the Lean theorem (e.g., `Chess.Proofs.symmetryTheorem`)
   - For cited reductions, link to the paper/source (e.g., "Shannon 1950, doi:...")
   - Explain the reduction mechanism briefly

4. **Update Status** — Use one of:
   - `"proven"` — Backed by a Lean theorem in this repository
   - `"cited"` — Backed by a peer-reviewed publication
   - `"known"` — Well-established but not yet proven here
   - `"conjectured"` — Plausible but unproven

5. **Integrate into Baseline** — Add your reduction to the appropriate list in `SearchSpace.lean` (`baseline`, or create a new category if needed).

6. **Verify Output** — Run `lake exe searchSpace` to see the updated report.

## Usage Examples

### Deriving SAN from Arbitrary Boards

To generate Standard Algebraic Notation for moves from a custom position:

```lean
-- Start from a FEN string
def customPosition : Except String GameState :=
  Parsing.parseFEN "r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1"

-- Get all legal moves and convert to SAN
def legalSanMoves : Except String (List String) := do
  let gs ← customPosition
  let moves := gs.legalMoves
  pure (moves.map (Parsing.moveToSAN gs))

#eval legalSanMoves
-- Outputs: ["O-O", "O-O-O", "Rh1", "Rf1", "Rg1", ...]
```

From the command line:
```bash
lake exe chessDemo -- --fen "r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1" --export-san moves.txt
```

### Loading PGN Files

To parse and replay a complete game from a PGN file:

```lean
-- Parse PGN with tags and moves
def loadGame (pgn : String) : Except String PGNGame := do
  Parsing.playPGNStructured pgn

-- Example: Load and check final position
def analyzePGN : Except String (String × Bool × Option String) := do
  let game ← loadGame "[Event \"Example\"]\n1. e4 e5 2. Nf3 Nc6"
  let fen := Parsing.toFEN game.finalState
  let inCheck := Rules.inCheckStatus game.finalState
  pure (fen, inCheck, game.result)

#eval analyzePGN
```

From the command line:
```bash
lake exe chessDemo -- --pgn-file game.pgn
lake exe chessDemo -- --pgn-file game.pgn --stream-moves  # Show move-by-move commentary
lake exe chessDemo -- --pgn-file game.pgn --export-pgn copy.pgn  # Copy/normalize
```

### Exporting FEN Snapshots

To serialize a game state to FEN format:

```lean
-- Build a position and export to FEN
def exportPosition : String :=
  let gs := buildStartingState
  Parsing.toFEN gs

#eval exportPosition
-- Outputs: "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

-- Apply moves and export
def positionAfterMoves : Except String String := do
  let start := buildStartingState
  let gs ← Parsing.applySANs start ["e4", "e5", "Nf3"]
  pure (Parsing.toFEN gs)

#eval positionAfterMoves
```

From the command line:
```bash
lake exe chessDemo -- --fen-file input.fen --export-fen output.fen
lake exe chessDemo -- --pgn-file game.pgn --export-fen final.fen
```

### Using the searchSpace Executable

The `searchSpace` program outputs the current catalog of perfect-game search-space estimates:

```bash
lake exe searchSpace
```

Output format:
```
10^120 — Raw move-tree baseline (known): Upper bound assuming ~35 legal moves per ply across 120 plies (Shannon's estimate).
```

Each line follows the pattern:
```
<estimate> — <label> (<status>): <notes>
```

Where:
- `estimate`: Scientific notation for search-space size
- `label`: Short description of the reduction
- `status`: One of `proven`, `cited`, `known`, `conjectured`
- `notes`: Proof/citation reference and explanation

To add a new reduction, edit `Chess/SearchSpace.lean` and ensure your entry includes:
1. A formal proof (link to theorem) OR a peer-reviewed citation
2. Clear explanation of the reduction mechanism
3. Appropriate status tag

Run `lake exe searchSpace` after updates to verify the output formatting.

## Formal Proof Requirement

Executable tests give fast feedback, but the repository goal is a fully proven model of chess. Every new rule, parser, or helper must ultimately be justified by Lean theorems that state the intended invariant (legal move equivalence, draw conditions, parser soundness, etc.) and prove it from first principles. When you add behavior, pair it with the necessary definitions/lemmas so that the proof footprint grows alongside the implementation—tests alone are no longer sufficient.

- Initial lemmas live alongside the code; for example, `simulateMove_board`/`simulateMove_history` in `Chess/Game.lean` show that previews share the same board/clock state as `movePiece` while freezing history. Keep documenting new declarations in the "Formal Proofs" section above (and in `CLAUDE.md`) so the proof backlog is traceable.
- The objective here is not to solve chess outright. The aim is to algorithmically shrink the solvable search space as far as possible, with each reduction accompanied by proofs that justify the pruning.
