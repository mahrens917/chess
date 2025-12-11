import Lake
open Lake DSL

package «chess» where

lean_lib «Chess» where

lean_lib «Tests» where
  roots := #[`Test.Runner, `Test.Main, `SlowTests.Perft]

lean_exe «chessDemo» {
  root := `Chess.Demo
}

lean_exe «searchSpace» {
  root := `Chess.SearchSpaceReport
}

@[test_driver]
lean_exe «test» {
  root := `Test.TestDriver
}
