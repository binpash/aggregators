import Synthesis

/- Aggregator for sort -/

abbrev Input := String

def parseInput (lines : List String) : List Input :=
  lines

def cmp (a b : Input) : Bool := a <= b

def mergeUnique (xs ys : List String) : List String :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then
      mergeUnique xs (y :: ys)
    else if x > y then
      y :: mergeUnique (x :: xs) (ys)
    else
      x :: mergeUnique xs (y :: ys)

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let lines ← readFile stream []
      let inputs := parseInput lines
      let acc := mergeUnique acc inputs
      pure acc) 
      [] streams

  output.forM (fun output => IO.print output)
  return 0
