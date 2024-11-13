import Synthesis

/- Aggregator for sort -n -/

abbrev Input := String

def parseInput (lines : List String) : Input :=
  lines.foldl (fun acc line => acc.append line) ""

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let lines ← readFile stream []
      let input := parseInput lines
      let acc := concat acc input
      pure acc) 
      "" streams

  IO.print output
  return 0
