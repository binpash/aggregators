import Synthesis

/- Aggregator to sum
   Nat -> Nat -/

def parseInput (lines : List String) : Nat :=
  lines.foldl (fun acc line => acc + line.trim.toNat!) 0

def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM
    (fun acc stream => do
      let lines ← readFileByLine stream
      let input := parseInput lines.toListImpl
      let acc := sum_agg acc input
      pure acc)
    0 streams

  IO.println output
  return 0
