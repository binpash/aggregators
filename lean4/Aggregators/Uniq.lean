import Synthesis

/- Aggregator for uniq -/
-- WARNING: assume uniq is preceded by sort

def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := uniq_agg acc lines.toListImpl
      pure acc) 
    [] streams

  output.forM (fun output => IO.print output)
  return 0
