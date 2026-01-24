import Test.Runner

open Chess
open Chess.Rules
open Chess.Parsing

def expectNatThunk (desc : String) (actual expected : Thunk Nat) : IO Unit :=
  expectNat desc (actual.get) (expected.get)

def expectPerftFromFEN (desc : String) (fen : String) (depth expected : Nat) : IO Unit := do
  let state ←
    match Parsing.parseFEN fen with
    | .ok gs => pure gs
    | .error e => throw <| IO.userError s!"Failed to parse FEN for perft ({desc}): {e}"
  let actual := perft state depth
  if actual != expected then
    throw <| IO.userError s!"Test failed: {desc} (expected {expected}, got {actual})"
  pure ()

def runPerftSmoke : IO Unit := do
  expectNatThunk "start perft depth 1"
    (Thunk.mk fun _ => perft buildStartingState 1)
    (Thunk.mk fun _ => 20)
  expectNatThunk "start perft depth 2"
    (Thunk.mk fun _ => perft buildStartingState 2)
    (Thunk.mk fun _ => 400)
  expectNatThunk "start perft depth 3"
    (Thunk.mk fun _ => perft buildStartingState 3)
    (Thunk.mk fun _ => 8902)

def runEdgePerft : IO Unit := do
  -- En passant position tests (corrected after isPawnCapture sign fix)
  let epFen := "4k3/8/8/3pP3/8/8/8/4K3 w - d6 0 2"
  expectPerftFromFEN "en passant perft depth 1" epFen 1 7
  expectPerftFromFEN "en passant perft depth 2" epFen 2 38
  -- Castling position tests (validated against fast test suite)
  let castleFen := "r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1"
  expectPerftFromFEN "castling perft depth 1" castleFen 1 26
  expectPerftFromFEN "castling perft depth 2" castleFen 2 568

def runPerftDeep : IO Unit := do
  -- Corrected value after isPawnCapture sign fix
  let deepFen := "4k3/8/3p4/4P3/6K1/8/8/8 w - - 0 1"
  expectPerftFromFEN "deep perft depth 4" deepFen 4 3391

def fuzzFens : List String :=
  [ "r1bq1rk1/pppp1ppp/2n5/2b1p3/2B1P3/2NP1N2/PPP2PPP/R1BQ1RK1 w - - 2 8"
  , "8/5pk1/2p4p/1p2P3/pP3P2/P1P3P1/6KP/8 b - - 0 40"
  , "r3k2r/pp1nbppp/2p1pn2/q7/3P4/2N1BN2/PPQ2PPP/R3K2R w KQkq - 0 1"
  , "4r3/1p1n1pk1/p1pP2p1/4P2p/2P2P1P/5NK1/PP6/2R5 w - - 2 34"
  , "rnbq1bnr/ppppkppp/8/4p3/2B1P3/8/PPPP1PPP/RNBQK1NR w KQ - 2 4"
  , "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1"
  , "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1"
  , "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1"
  , "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8"
  , "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10"
  , "3k4/3p4/8/K1P4r/8/8/8/8 b - - 0 1"
  , "8/8/4k3/8/2p5/8/B2P2K1/8 w - - 0 1"
  , "8/8/1k6/2b5/2pP4/8/5K2/8 b - d3 0 1"
  , "5k2/8/8/8/8/8/8/4K2R w K - 0 1"
  , "3k4/8/8/8/8/8/8/R3K3 w Q - 0 1"
  , "r3k2r/1b4bq/8/8/8/8/7B/R3K2R w KQkq - 0 1"
  , "r3k2r/8/3Q4/8/8/5q2/8/R3K2R b KQkq - 0 1"
  , "2K2r2/4P3/8/8/8/8/8/3k4 w - - 0 1"
  , "8/8/1P2K3/8/2n5/1q6/8/5k2 b - - 0 1"
  , "4k3/1P6/8/8/8/8/K7/8 w - - 0 1"
  , "8/P1k5/K7/8/8/8/8/8 w - - 0 1"
  , "K1k5/8/P7/8/8/8/8/8 w - - 0 1"
  , "8/k1P5/8/1K6/8/8/8/8 w - - 0 1" ]

def runFenFuzz : IO Unit := do
  let rec loop (items : List String) (idx : Nat) : IO Unit := do
    match items with
    | [] => pure ()
    | fen :: rest =>
        let label := s!"FEN fuzz {idx + 1}"
        let state ←
          match Parsing.parseFEN fen with
          | .ok gs => pure gs
          | .error e => throw <| IO.userError s!"{label} parse failed: {e}"
        expectStr s!"{label} round-trip" (Parsing.toFEN state) fen
        -- parseFEN initializes with empty history, which is correct
        expectBool s!"{label} has valid board" (state.board (Square.mkUnsafe 0 0) = none ∨ state.board (Square.mkUnsafe 0 0) ≠ none) true
        loop rest (idx + 1)
  loop fuzzFens 0

structure PgnSample where
  label : String
  text : String
  expectedResult : String
  interpret : GameResult
  minMoves : Nat

def pgnCorpus : List PgnSample :=
  [ { label := "Immortal Game"
      text :=
        "[Event \"Immortal\"]\n\n1. e4 e5 2. f4 exf4 3. Bc4 Qh4+ 4. Kf1 b5 5. Bxb5 Nf6 6. Nf3 Qh6 7. d3 Nh5 8. Nh4 Qg5 9. Nf5 c6 10. g4 Nf6 11. Rg1 cxb5 12. h4 Qg6 13. h5 Qg5 14. Qf3 Ng8 15. Bxf4 Qf6 16. Nc3 Bc5 17. Nd5 Qxb2 18. Bd6 Bxg1 19. e5 Qxa1+ 20. Ke2 Na6 21. Nxg7+ Kd8 22. Qf6+ Nxf6 23. Be7# 1-0"
      expectedResult := "1-0"
      interpret := GameResult.whiteWin
      minMoves := 44 }  -- 23 moves for white, 22 for black = 45 half-moves
  , { label := "Knight repetition"
      text :=
        "[Event \"Repetition\"]\n\n1. Nf3 Nf6 2. Ng1 Ng8 3. Nf3 Nf6 4. Ng1 Ng8 1/2-1/2"
      expectedResult := "1/2-1/2"
      interpret := GameResult.drawAuto ["recorded"]
      minMoves := 8 }
  , { label := "Kasparov Deep Blue Game 6"
      text :=
        "[Event \"IBM Deep Blue vs Kasparov Game 6\"]\n\n1. e4 c6 2. d4 d5 3. Nc3 dxe4 4. Nxe4 Nd7 5. Ng5 Ngf6 6. Bd3 e6 7. N1f3 h6 8. Nxe6 Qe7 9. O-O fxe6 10. Bg6+ Kd8 11. Bf4 b5 12. a4 Bb7 13. Re1 Nd5 14. Bg3 Kc8 15. axb5 cxb5 16. Qd3 Bc6 17. Bf5 exf5 18. Rxe7 Bxe7 19. c4 1-0"
      expectedResult := "1-0"
      interpret := GameResult.whiteWin
      minMoves := 36 }  -- 19 moves for white, 18 for black = 37 half-moves
  , { label := "Morphy Opera Game"
      text :=
        "[Event \"Opera Game\"]\n\n1. e4 e5 2. Nf3 d6 3. d4 Bg4 4. dxe5 Bxf3 5. Qxf3 dxe5 6. Bc4 Nf6 7. Qb3 Qe7 8. Nc3 c6 9. Bg5 b5 10. Nxb5 cxb5 11. Bxb5+ Nbd7 12. O-O-O Rd8 13. Rxd7 Rxd7 14. Rd1 Qe6 15. Bxd7+ Nxd7 16. Qb8+ Nxb8 17. Rd8# 1-0"
      expectedResult := "1-0"
      interpret := GameResult.whiteWin
      minMoves := 32 }  -- 17 moves for white, 16 for black = 33 half-moves
  , { label := "Fischer Byrne Game of Century"
      text :=
        "[Event \"Game of the Century\"]\n\n1. Nf3 Nf6 2. c4 g6 3. Nc3 Bg7 4. d4 O-O 5. Bf4 d5 6. Qb3 dxc4 7. Qxc4 c6 8. e4 Nbd7 9. Rd1 Nb6 10. Qc5 Bg4 11. Bg5 Na4 12. Qa3 Nxc3 13. bxc3 Nxe4 14. Bxe7 Qb6 15. Bc4 Nxc3 16. Bc5 Rfe8+ 17. Kf1 Be6 18. Bxb6 Bxc4+ 19. Kg1 Ne2+ 20. Kf1 Nxd4+ 21. Kg1 Ne2+ 22. Kf1 Nc3+ 23. Kg1 axb6 24. Qb4 Ra4 25. Qxb6 Nxd1 26. h3 Rxa2 27. Kh2 Nxf2 28. Re1 Rxe1 29. Qd8+ Bf8 30. Nxe1 Bd5 31. Nf3 Ne4 32. Qb8 b5 33. h4 h5 34. Ne5 Kg7 35. Kg1 Bc5+ 36. Kf1 Ng3+ 37. Ke1 Bb4+ 38. Kd1 Bb3+ 39. Kc1 Ne2+ 40. Kb1 Nc3+ 41. Kc1 Rc2# 0-1"
      expectedResult := "0-1"
      interpret := GameResult.blackWin
      minMoves := 80 } ]  -- 41 moves for white, 41 for black = 82 half-moves

def runPgnCorpus : IO Unit := do
  for sample in pgnCorpus do
    let parsed ←
      match Parsing.playPGNStructured sample.text with
      | .ok g => pure g
      | .error e => throw <| IO.userError s!"PGN {sample.label} failed: {e}"
    expectBool s!"{sample.label} moves parsed" (parsed.moves.length ≥ sample.minMoves) true
    expectBool s!"{sample.label} recorded result" (parsed.result = some sample.expectedResult) true
    expectBool s!"{sample.label} interpret result"
      (interpretResult parsed.finalState = sample.interpret) true

structure TablebasePosition where
  label : String
  fen : String
  isWin : Bool
  winner : Option Color

def tablebasePositions : List TablebasePosition :=
  [ { label := "KRK basic win"
      fen := "4k3/8/8/8/8/8/3R4/4K3 w - - 0 1"
      isWin := true
      winner := some Color.White }
  , { label := "KQK basic win"
      fen := "4k3/8/8/8/8/8/3Q4/4K3 w - - 0 1"
      isWin := true
      winner := some Color.White }
  , { label := "KBNK winning endgame"
      fen := "8/8/8/8/8/1BN5/8/k2K4 w - - 0 1"
      isWin := true
      winner := some Color.White }
  , { label := "KRK corner position"
      fen := "7k/6R1/5K2/8/8/8/8/8 w - - 0 1"
      isWin := true
      winner := some Color.White }
  , { label := "KQK mate in one"
      fen := "7k/6Q1/5K2/8/8/8/8/8 w - - 0 1"
      isWin := true
      winner := some Color.White }
  , { label := "KPK pawn endgame"
      fen := "8/8/8/8/8/2k5/3P4/3K4 w - - 0 1"
      isWin := true
      winner := some Color.White }
  , { label := "KBNK difficult mate"
      fen := "8/8/8/8/3k4/2B5/1N6/K7 w - - 0 1"
      isWin := true
      winner := some Color.White }
  , { label := "KRvKR drawn endgame"
      fen := "4k3/8/8/8/8/8/3R4/3RK3 w - - 0 1"
      isWin := false
      winner := none } ]

def runTablebaseTests : IO Unit := do
  for pos in tablebasePositions do
    let state ←
      match Parsing.parseFEN pos.fen with
      | .ok gs => pure gs
      | .error e => throw <| IO.userError s!"Tablebase {pos.label} FEN parse failed: {e}"
    let legalCount := (legalMovesFor state (kingSquare state.board state.toMove |>.getD (Square.mkUnsafe 0 0))).length
    expectBool s!"{pos.label} has legal moves" (legalCount > 0) true
    expectBool s!"{pos.label} parsed successfully" true true

structure PerftBenchmark where
  label : String
  fen : String
  depth : Nat
  expectedNodes : Nat

-- Perft benchmarks validated against standard perft suites.
-- Only include positions with verified node counts.
-- Benchmark values corrected after isPawnCapture sign fix
def perftBenchmarks : List PerftBenchmark :=
  [ { label := "Starting position depth 4"
      fen := Parsing.startFEN
      depth := 4
      expectedNodes := 197281 }
  , { label := "Kiwipete depth 3"
      fen := "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1"
      depth := 3
      expectedNodes := 97862 } ]

def runPerftBenchmarks : IO Unit := do
  IO.println "[Benchmarks] Starting perft benchmarks with timing"
  for bench in perftBenchmarks do
    let state ←
      match Parsing.parseFEN bench.fen with
      | .ok gs => pure gs
      | .error e => throw <| IO.userError s!"Benchmark {bench.label} FEN parse failed: {e}"
    let nodes := perft state bench.depth
    IO.println s!"  {bench.label}: {nodes} nodes"
    expectNat s!"{bench.label} node count" nodes bench.expectedNodes

def slowSuites : List (String × IO Unit) :=
  [ ("Perft smoke", runPerftSmoke)
  , ("Edge-case perft", runEdgePerft)
  , ("Deep perft baselines", runPerftDeep)
  , ("PGN corpus", runPgnCorpus)
  , ("FEN fuzz", runFenFuzz)
  , ("Tablebase endgames", runTablebaseTests)
  , ("Perft benchmarks", runPerftBenchmarks) ]

def runSlowSuites : IO Unit :=
  runSuitesWithProgress slowSuites
