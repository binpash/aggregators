import Synthesis
import Init.Data.String

/- Aggregator for sort -n -/

structure Input where
  key   : Nat 
  value : String
  deriving Repr 

instance : ToString Input where 
  toString : Input → String
  | ⟨key, value⟩ => s!" {key} {value}"

def parseInput (lines : List String) : List Input :=
  lines.map (fun line => 
    let trimmed := String.trimLeft line
    let key := trimmed.takeWhile (λ c => c.isDigit)
    let count := key.toNat!
    ⟨count, trimmed.drop key.length⟩
  )

def uniqCAggregator (xs ys : List Input) : List Input :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs, y :: ys => 
    if x.value == y.value then
      ⟨x.key + y.key, x.value⟩ :: uniqCAggregator xs ys
    else if x.value <= y.value then
      x :: uniqCAggregator xs (y :: ys)
    else
      y :: uniqCAggregator (x :: xs) ys

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let lines ← readFile stream []
      let inputs := parseInput lines
      let acc := uniqCAggregator acc inputs
      pure acc) 
      [] streams

  output.forM (fun output => IO.print output)
  return 0

