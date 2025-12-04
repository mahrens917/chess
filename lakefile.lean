import Lake
open Lake DSL

package «chess» where

lean_lib «Chess» where

lean_exe «chessDemo» {
  root := `Chess.Demo
}

@[test_driver]
lean_exe «test» {
  root := `Test.Main
}
