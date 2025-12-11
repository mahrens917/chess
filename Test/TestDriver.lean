import Test.Runner
import SlowTests.Perft

unsafe def main : IO Unit := do
  runFastSuites
  runSlowSuites
