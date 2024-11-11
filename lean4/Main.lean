import Verification

def main (args : List String) : IO UInt32 := do
  -- let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  -- let streams ← getAllStreams args
  --
  -- let output ← List.foldlM (fun acc stream => do
  --     let lines ← readFile stream []
  --     let inputs := parseInput lines
  --     let acc := merge (fun a b => a.key <= b.key) acc inputs
  --     pure acc) 
  --     [] streams
  --
  -- output.forM (fun output => IO.print output)
  return 0
