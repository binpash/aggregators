import Synthesis

/- Aggregator for sort -k 1 -n -/

structure Input where
  key   : Option Float
  input : String
  deriving Repr

instance : ToString Input where
  toString : Input → String
  | ⟨_, input⟩ => input

def parseInput (lines : List String) : List Input :=
  lines.map (fun line =>
    let key := getFirstNumber line
    ⟨key, line⟩
  )

def cmp (a b : Input) : Bool :=
  match a.key, b.key with
  | none, none => a.input <= b.input
  | none, some _ => true
  | some _, none => false
  | some a_key, some b_key =>
    if a_key == b_key then
      a.input <= b.input
    else
      a_key < b_key

def main (args : List String) : IO UInt32 := do
  let streams ← getAllStreams args
  let output ← List.foldlM
    (fun acc stream => do
      let lines ← readFileByLine stream
      let inputs := parseInput lines.toListImpl
      let acc := mergeArrayAgg cmp acc inputs
      pure acc)
    [] streams

  output.forM (fun output => IO.print output)
  return 0
