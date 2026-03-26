import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package «chess» where

lean_lib «Chess» where

@[default_target]
lean_lib «Tests» where
  roots := #[`ChessTest.Runner, `ChessTest.Main, `SlowTests.Perft]

lean_exe «chessDemo» {
  root := `Chess.Demo
}

lean_exe «searchSpace» {
  root := `Chess.SearchSpaceReport
}

@[test_driver]
lean_exe «test» {
  root := `ChessTest.TestDriver
}
