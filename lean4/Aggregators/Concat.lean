import Synthesis

def concat_agg (acc x : ByteArray) : ByteArray := 
  acc ++ x

def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM 
    (fun acc stream => do
      let bytes ← readString stream ByteArray.empty
      let acc := concat_agg acc bytes
      pure acc) 
    ByteArray.empty streams

  let stdout ← IO.getStdout
  stdout.write output
  return 0
