def concatAgg : (x y : ByteArray) → ByteArray :=
 ByteArray.append

def sumAgg : (x y : Nat) → Nat :=
  Nat.add

def uniqAgg (xs ys : List String)  : List String :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then x :: uniqAgg xs ys
    else x :: uniqAgg xs (y :: ys)

/-- For sort -u -/
def mergeUniqAgg (xs ys : List String) : List String :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x == y then
      mergeUniqAgg xs (y :: ys)
    else if x > y then
      y :: mergeUniqAgg (x :: xs) (ys)
    else
      x :: mergeUniqAgg xs (y :: ys)

/-- Array-based tail recursive implementation -/
def mergeAuxArray (acc : Array α) (le : α → α → Bool) (xs ys : Array α) : Array α :=
if h : xs.size = 0 then ys ++ acc.reverse
else if h2 : ys.size = 0 then xs ++ acc.reverse
else if le xs[xs.size - 1] ys[ys.size - 1]
  then mergeAuxArray (acc.push ys[ys.size - 1]) le xs ys.pop
  else mergeAuxArray (acc.push xs[xs.size - 1]) le xs.pop ys
termination_by (xs.size, ys.size)

def mergeArrayAgg (le : α → α → Bool) (xs ys : List α) : List α :=
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

def mergeListAgg(le : α → α → Bool) (xs ys : List α) : List α :=
  mergeAuxList [] le xs ys

/-- WARNING: The non-tail recursive implementation of merge
    causes stack overflow. This is used for proofs in
    Verification/Sort.lean -/
def mergeListAggNTR (le : α → α → Bool) (xs ys : List α) : List α :=
   match xs, ys with
   | [], ys => ys
   | xs, [] => xs
   | x :: xs, y :: ys =>
     if le x y then
       x :: mergeListAggNTR le xs (y :: ys)
     else
       y :: mergeListAggNTR le (x :: xs) ys

-- This is for parsing numbers from a string in the sort aggregators
def getFirstNumber (s : String) : Option Float :=
  let chars := (((s.trim).splitOn "," )[0]!).toList

  let rec preprocess (chars : List Char) (acc : String) (exponent : Nat) (decimal_used : Bool) : Option Float :=
    match chars with
    | [] =>
      if acc.isEmpty then
        none
      else
        some (OfScientific.ofScientific (String.toNat! acc) true exponent)

    | c :: cs =>
      if '0' ≤ c ∧ c ≤ '9' then
        if decimal_used then
          preprocess cs (acc.push c) (exponent + 1) decimal_used
        else
          preprocess cs (acc.push c) exponent decimal_used

      else if (c = ',') ∧ ¬acc.isEmpty ∧ ¬decimal_used then
        preprocess cs acc exponent decimal_used

      else if (c = '.') ∧ ¬decimal_used then
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

-- #eval getFirstNumber ""
-- #eval getFirstNumber "1"
-- #eval getFirstNumber "12"
-- #eval getFirstNumber "12.3"
-- #eval getFirstNumber "12.34"
--
-- #eval getFirstNumber "a"
-- #eval getFirstNumber "a1"
-- #eval getFirstNumber "1a"
--
-- #eval getFirstNumber "123.456"
-- #eval getFirstNumber "123,456"
-- #eval getFirstNumber "1,23,456"
-- #eval getFirstNumber "1,23.456"
-- #eval getFirstNumber "1.23,456"
