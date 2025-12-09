import SlowTests.Perft

unsafe def main : IO Unit := do
  IO.println "[Suites] Running slow perft suites"
  runSlowSuites
