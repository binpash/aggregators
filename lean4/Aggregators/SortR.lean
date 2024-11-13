import Synthesis

/- Aggregator for sort -/

abbrev Input := String

def parseInput (lines : List String) : List Input :=
  lines

def cmp (a b : Input) : Bool := a >= b

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let lines ← readFile stream []
      let inputs := parseInput lines
      let acc := merge cmp acc inputs
      pure acc) 
      [] streams

  output.forM (fun output => IO.print output)
  return 0
