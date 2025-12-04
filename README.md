# Chess: Lean 4 Formalization of Standard Chess Rules

This repository builds a Lean 4 model of the classic chess game: board geometry, pieces, movement predicates, and the core game state logic.

## Layout

- `Chess/Core.lean` defines files/ranks, squares, colors, pieces, boards, and the `GameState` structure.
- `Chess/Movement.lean` encodes each piece's legal moves and includes helper lemmas about those movements.
- `Chess/Game.lean` updates the board, tracks turns, and proves board-update invariants.
- `Chess/Demo.lean` exercises the board helpers via `#eval` expressions and powers a lightweight executable.

## Build

```bash
lake build
lake exe run chessDemo
```

The `chessDemo` executable prints algebraic square names, king/knight targets, and move-state details defined in `Chess/Demo.lean`.
