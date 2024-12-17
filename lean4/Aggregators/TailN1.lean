import Synthesis

/- Aggregator for tail -n 1 -/

def main (args : List String) : IO UInt32 := do
  let stream ← getLastStream args
  let lines ← readFileByLine stream
  let output := lines[0]!
  IO.print output
  return 0
