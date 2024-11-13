import Synthesis

/- Aggregator for sort -n -/

abbrev Input := Nat

def parseInput (lines : List String) : Input :=
  lines.foldl (fun acc line => acc + line.trim.toNat!) 0

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
    let lines ← readFile stream []
    let input := parseInput lines
    let acc := sum acc input
    pure acc) 
    (0 : Input) streams

  IO.println output
  return 0
