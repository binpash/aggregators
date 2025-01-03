
import Synthesis





def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM 
    (fun acc stream => do
      let bytes ← readFile stream ByteArray.empty
      let acc := concatAgg acc bytes
      pure acc)
    ByteArray.empty streams
  let stdout ← IO.getStdout
  stdout.write output
  return 0
