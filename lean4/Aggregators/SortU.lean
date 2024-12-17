import Synthesis

/- Aggregator for sort -u -/

def cmp (a b : String) : Bool := a <= b

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
  let streams ← getAllStreams args

  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := mergeUnique acc lines.toListImpl
      pure acc) 
    [] streams

  output.forM (fun output => IO.print output)
  return 0
