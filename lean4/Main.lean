import Synthesis
def main (args : List String) : IO UInt32 := do
  let stream ← getFirstStream args
  let line ← stream.getLine
  IO.print line
  return 0
