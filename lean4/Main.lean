
import Synthesis





def main (args : List String) : IO UInt32 := do
  let stream ← getLastStream args
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := None acc lines.toListImpl
      pure acc)
    [] streams
  IO.println output
  return 0
