def concat : (x y : ByteArray) → ByteArray :=
 ByteArray.append

def sum : (x y : Nat) → Nat :=
  Nat.add

def uniq_agg (xs ys : List String)  : List String :=
  match xs, ys with 
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then x :: uniq_agg xs ys
    else x :: uniq_agg xs (y :: ys)

/-- Array-based tail recursive implementation -/
def mergeAuxArray (acc : Array α) (le : α → α → Bool) (xs ys : Array α) : Array α :=
if h : xs.size = 0 then ys ++ acc.reverse
else if h2 : ys.size = 0 then xs ++ acc.reverse
else if le xs[xs.size - 1] ys[ys.size - 1]
  then mergeAuxArray (acc.push ys[ys.size - 1]) le xs ys.pop
  else mergeAuxArray (acc.push xs[xs.size - 1]) le xs.pop ys
termination_by (xs.size, ys.size)

def merge (le : α → α → Bool) (xs ys : List α) : List α :=
mergeAuxArray #[] le xs.toArray ys.toArray |>.toList

/-- List-based tail recursive implementation -/
def mergeAuxList (acc : List α) (le : α → α → Bool) (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => acc.reverse ++ ys
  | xs, [] => acc.reverse ++ xs
  | x :: xs, y :: ys =>
    if le x y then
      mergeAuxList (x::acc) le xs (y :: ys)
    else
      mergeAuxList (y::acc) le (x :: xs) ys

def mergeList (le : α → α → Bool) (xs ys : List α) : List α :=
  mergeAuxList [] le xs ys

/- Non-tail recursive implementation causes stack overflow
def merge (le : α → α → Bool) (xs ys : List α) : List α :=
   match xs, ys with
   | [], ys => ys
   | xs, [] => xs
   | x :: xs, y :: ys =>
     if le x y then
       x :: merge le xs (y :: ys)
     else
       y :: merge le (x :: xs) ys
-/

-- This is for parsing numbers from a string in the sort aggregators
def is_digit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def is_thousand_separator (c : Char) : Bool :=
  c = ','

def is_decimal_point (c : Char) : Bool :=
  c = '.'

def get_first_number (s : String) : Option Float :=
  let chars := (((s.trim).splitOn "," )[0]!).toList

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

