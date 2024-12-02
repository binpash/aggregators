def concat : (x y : String) → String :=
 String.append

def sum : (x y : Nat) → Nat :=
  Nat.add

def merge (le : α → α → Bool) (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then
      x :: merge le xs (y :: ys)
    else
      y :: merge le (x :: xs) ys
