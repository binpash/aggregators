import Synthesis

/- Aggregator for sort -n -/

structure Input where
  value : String
  deriving Repr 

instance : ToString Input where 
  toString : Input → String
  | ⟨input⟩ => input 

def parseInput (lines : List String) : Input :=
  lines.foldl (fun acc line => ⟨acc.value.append line⟩) ⟨""⟩

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let lines ← readFile stream []
      let input := parseInput lines
      let acc := concat acc input.value
      pure acc) 
      "" streams

  IO.print output
  return 0
