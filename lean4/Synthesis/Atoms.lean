def concat : (x y : String) → String :=
 String.append

def sum : (x y : Nat) → Nat :=
  Nat.add

/-
Array-based tail recursive implementation
-/

def mergeAuxArray (acc : Array α) (le : α → α → Bool) (xs ys : Array α) : Array α :=
if h : xs.size = 0 then ys ++ acc.reverse
else if h2 : ys.size = 0 then xs ++ acc.reverse
else if le xs[xs.size - 1] ys[ys.size - 1]
  then mergeAuxArray (acc.push ys[ys.size - 1]) le xs ys.pop
  else mergeAuxArray (acc.push xs[xs.size - 1]) le xs.pop ys
termination_by (xs.size, ys.size)

def merge (le : α → α → Bool) (xs ys : List α) : List α :=
mergeAuxArray #[] le xs.toArray ys.toArray |>.toList


/-
List-based tail recursive implementation
-/
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











-- def merge (le : α → α → Bool) (xs ys : List α) : List α :=
--   match xs, ys with
--   | [], ys => ys
--   | xs, [] => xs
--   | x :: xs, y :: ys =>
--     if le x y then
--       x :: merge le xs (y :: ys)
--     else
--       y :: merge le (x :: xs) ys
