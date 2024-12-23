
import Synthesis





def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := uniq_agg acc lines.toListImpl
      pure acc)
    [] streams
  output.forM (fun line => IO.print line)
  return 0
