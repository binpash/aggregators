import Aggregators

/-- Aggregator for sort -n -/
def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
    let lines ← readFile stream []
    let inputs := parseInput lines
    let acc := merge (fun a b => a.key <= b.key) acc inputs
    pure acc) 
    [] streams
  
  output.forM (fun output => IO.print output)
  return 0

/- Tests
#eval main ["test.txt", "test2.txt"]
sort -n test.txt test2.txt > theirs.txt && .lake/build/bin/aggregatorstest.txt test2.txt > mine.txt && diff mine.txt theirs.txt
#eval merge (fun a b => a <= b) [1, 3, 5] [2, 4, 6] -/
