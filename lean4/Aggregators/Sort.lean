import Synthesis

/- Aggregator for sort -/

def cmp (a b : String) : Bool := a <= b

def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM
    (fun acc stream => do
      let lines ← (readFileByLine stream)
      let acc := mergeArrayAgg cmp acc lines.toListImpl
      pure acc)
    [] streams

  output.forM (fun output => IO.print output)
  return 0
