import Synthesis

/- Aggregator for sort -n -/

abbrev Input := String

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let bytes ← readString stream ByteArray.empty
      let acc := acc.append bytes
      pure acc) 
      ByteArray.empty streams

  let stdout ← IO.getStdout
  stdout.write output
  return 0
