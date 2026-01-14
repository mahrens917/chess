# Parser Proof Bar (FEN / SAN / PGN)

This repo has robust executable parsing/printing/replay for FEN/SAN/PGN, plus regression tests.

For “100% complete” claims, we need to choose an explicit proof bar for these formats because:
- some formats include ambiguous or presentation-only fields (spacing, comments, NAGs, tags)
- SAN has context-dependent disambiguation and check/mate suffixes

## Recommended Bar (pragmatic)

### FEN
- Prove: `parseFEN (toFEN gs) = .ok gs` for all well-formed `GameState` values that satisfy the repo’s invariants.
- Keep: negative tests for invalid FENs (already present).

### SAN
- Prove: for any legal move `m ∈ allLegalMoves gs`,
  `applySAN gs (moveToSAN gs m) = .ok (applyLegalMove gs m)` (or equivalent state update lemma).
- Keep: regression “roundtrip” tests (already present).

### PGN
- Prove: `playPGN (exportPGN gs …) = .ok …` is usually too strong unless export is canonical.
- Recommended: a weaker theorem about replaying exported move lists (ignoring comments/tags).

## Engine/Tooling Compatibility Bar (alternative)

Instead of full formal round-trips, choose:
- `lake test` includes a curated corpus of FEN/PGN fixtures
- A fuzz suite for FEN round-trips (already present in `SlowTests/Perft.lean`)
- A stable “export compatibility” guarantee documented in `API_GUIDE.md`

## Current Status

- Tests cover FEN round-trip on many fixtures and SAN/PGN smoke coverage.
- Fully formal parser round-trip theorems are still pending (see `CHECKLIST_ANALYTICAL_LIBRARY.md`).

