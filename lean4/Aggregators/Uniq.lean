import Synthesis

/- Aggregator for uniq -/
-- WARNING: assume uniq is preceded by sort

def uniq_aggregator (xs ys : List String)  : List String :=
  match xs, ys with 
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then x :: uniq_aggregator xs ys
    else x :: uniq_aggregator xs (y :: ys)

def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := uniq_aggregator acc lines.toListImpl
      pure acc) 
    [] streams

  output.forM (fun output => IO.print output)
  return 0
