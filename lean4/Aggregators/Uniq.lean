import Synthesis

/- Aggregator for uniq -/
-- WARNING: assume uniq is preceded by sort

abbrev Input := String

def parseInput (lines : List String) : List Input :=
  lines

def uniq_aggregator (xs ys : List String)  : List String :=
  match xs, ys with 
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then x :: uniq_aggregator xs ys
    else x :: uniq_aggregator xs (y :: ys)

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let lines ← readFile stream []
      let inputs := parseInput lines
      let acc := uniq_aggregator acc inputs
      pure acc) 
      [] streams

  output.forM (fun output => IO.print output)
  return 0
