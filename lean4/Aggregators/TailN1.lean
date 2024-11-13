import Synthesis

/- Aggregator for head -n 1 -/

abbrev Input := String

def parseInput (lines : List Input) : Input :=
    List.head! lines

def getLastStream (args : List String) : IO IO.FS.Stream :=
  match args.tail with
  | [] => throw $ IO.userError "No input files"
  | (arg :: _) => getFileStream arg

def main (args : List String) : IO UInt32 := do
  let stream ← getLastStream args
  let lines ← readFile stream []
  let output := parseInput lines
  IO.print output
  return 0
