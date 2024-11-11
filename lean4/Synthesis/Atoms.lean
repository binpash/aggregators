def merge (le : α → α → Bool) (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if le x y then
      x :: merge le xs (y :: ys)
    else
      y :: merge le (x :: xs) ys

-- def merge {α : Type} (r : α → α → Prop) [DecidableRel r] 
--   : List α → List α → List α
--   | [], l' => l'
--   | l, [] => l
--   | a :: l, b :: l' => if (r a b) then a :: merge r l (b :: l') else b :: merge r (a :: l) l'
