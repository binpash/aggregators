import Synthesis

/- Aggregator for sort -n -/

structure Input where
  key   : Option Float
  input : String
  deriving Repr 

instance : ToString Input where 
  toString : Input → String
  | ⟨_, input⟩ => input 

def is_digit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def is_thousand_separator (c : Char) : Bool :=
  c = ','

def is_decimal_point (c : Char) : Bool :=
  c = '.'

def get_first_number (s : String) : Option Float :=
  let chars := s.trim.toList

  let rec preprocess (chars : List Char) (acc : String) (exponent : Nat) (decimal_used : Bool) : Option Float :=
    match chars with
    | [] => 
      if acc.isEmpty then 
        none 
      else 
        some (OfScientific.ofScientific (String.toNat! acc) true exponent)

    | c :: cs =>
      if is_digit c then
        if decimal_used then
          preprocess cs (acc.push c) (exponent + 1) decimal_used
        else
          preprocess cs (acc.push c) exponent decimal_used

      else if is_thousand_separator c ∧ ¬acc.isEmpty ∧ ¬decimal_used then
        preprocess cs acc exponent decimal_used

      else if is_decimal_point c ∧ ¬decimal_used then
        preprocess cs acc exponent true

      else
        if acc.isEmpty then 
          none 
        else 
          some (OfScientific.ofScientific (String.toNat! acc) true exponent)

  match chars with
  | [] => none
  | c :: cs =>
    if c = '-' then
      preprocess cs "-" 0 false
    else
      preprocess chars "" 0 false

-- #eval get_first_number ""
-- #eval get_first_number "1"
-- #eval get_first_number "12"
-- #eval get_first_number "12.3"
-- #eval get_first_number "12.34"
--
-- #eval get_first_number "a"
-- #eval get_first_number "a1"
-- #eval get_first_number "1a"
--
-- #eval get_first_number "123.456"
-- #eval get_first_number "123,456"
-- #eval get_first_number "1,23,456"
-- #eval get_first_number "1,23.456"
-- #eval get_first_number "1.23,456"

def parseInput (lines : List String) : List Input :=
  lines.map (fun line => 
    let key := get_first_number line
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

-- instance : DecidableRel cmp := by sorry

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
  let streams ← getAllStreams args

  let output ← List.foldlM (fun acc stream => do
      let lines ← readFile stream []
      let inputs := parseInput lines
      let acc := merge cmp acc inputs
      pure acc) 
      [] streams

  output.forM (fun output => IO.print output)
  return 0

-- TODO: what is the right way to handle errors?
-- Can use error monad
-- def parseFloat (s : String) : Option Float :=
--   match Lean.Json.parse s with
--     | .ok (.num t) => some t.toFloat
--     | _ => none

