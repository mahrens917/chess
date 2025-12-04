# CLAUDE Instructions

## Project Intent
- This repository formalizes standard chess rules in Lean 4: squares, pieces, movement, and the core game state.
- The `Chess` library exports `Chess.Core`, `Chess.Movement`, `Chess.Game`, and a demo insulated by `Chess.Demo`.

## Testing Protocol
- Every change must run the full Lean toolchain: `lake fmt`, `lake build`, and `lake test`.
- The `test` executable is driven by `Test.Main` and covers board invariants, piece-target counts, pawn direction, and move-bookkeeping logic.
- Keep the tests updated whenever new functionality is added so that `lake test` continues to exercise `Chess.Core`, `Chess.Movement`, and `Chess.Game`.

## CI Expectations
- `ci.sh` stages work, uses Claude to craft a commit message, and pushes after running fmt/build/test.
- Since `lake test` now succeeds with the Chess test driver, the CI script assumes those commands pass before committing.

## Development Notes
- Lean’s built-in decidables are leveraged for filtering square lists, so new predicates should remain decidable to keep the demo/test harness working.
- When adding new executables or modules, update `lakefile.lean` and rerun `lake fmt/test`.
