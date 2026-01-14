# Perft Fixtures

This repo treats perft as both a regression suite (expected node counts) and a performance guardrail
(benchmarked depths).

## Where the fixtures live

- Fast perft checks: `Test/Runner.lean`
- Slow suites: `SlowTests/Perft.lean`
- Test driver (runs fast suites): `Test/TestDriver.lean`

## What to run

- `lake test` runs the fast suites (including fast perft checks).
- `lake exe slowtest` runs the slow perft baselines (including benchmarks).
- `lake exe chessDemo -- --fen "<fen>" --perft <d>` runs perft from the CLI demo.

## Current benchmark baselines (from `lake test` output)

- Starting position depth 3: 8902
- Starting position depth 4: 197281
- Kiwipete depth 3: 97983
 
Fast suites also cover depth-1 counts for en passant and castling fixtures.

For deeper, position-specific baseline counts, use the fixtures defined in `SlowTests/Perft.lean`.
