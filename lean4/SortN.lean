import Lean.Data.Json.Parser

/- UTILITIES -/

/- IO.FS.Stream represents a POSIX stream
  structure Stream where
    flush   : IO Unit
    read    : USize → IO ByteArray
    write   : ByteArray → IO Unit
    getLine : IO String
    putStr  : String → IO Unit
-/

def bufsize : USize := 20 * 1024

def exitWithError {α : Type} (errMsg : String) : IO α := do
  throw <| IO.userError errMsg

/-- Returns a stream for the given file, or none if the file does not exist.
    The file handle tracks the underlying file descriptor. 
    When there are no references to its value, a finalizer closes the file descriptor.
    It is given the same interface as a POSIX stream using IO.FS.Stream.ofHandle. -/
def getFileStream (filename : System.FilePath) : IO IO.FS.Stream := do
  let fileExists ← filename.pathExists
  if not fileExists then 
    exitWithError s!"File not found: {filename}"
  else 
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (IO.FS.Stream.ofHandle handle)

def getAllStreams (filenames : List System.FilePath) : IO (List IO.FS.Stream) := do
  filenames.mapM getFileStream

/-- Reads from the stream and writes to stdout until the stream is empty. -/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

/-- Reads from the stream and returns a list of lines. -/
partial def readFile (stream : IO.FS.Stream) (buf : List String) : IO (List String) := do
  let line ← stream.getLine
  if line.isEmpty then
    pure buf
  else
    let mut buf := buf.append [line]
    readFile stream buf

/-- Reads from the list of streams and returns a list of all lines. -/
partial def readAll (streams : List IO.FS.Stream) (buf : List String) : IO (List String) := do
  match streams with
  | [] => pure buf
  | stream :: rest => 
    let buf ← readFile stream buf
    readAll rest buf

/- SORTING -/

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

-- TODO: what is the right way to handle errors?
-- Can use error monad
def parseFloat (s : String) : Option Float :=
  match Lean.Json.parse s with
    | .ok (.num t) => some t.toFloat
    | _ => none

def get_first_number (s : String) : Option Float :=
  let chars := s.trim.toList
  let rec preprocess (chars : List Char) (acc : String) (decimal_used : Bool) : Option String :=
    match chars with
    | [] => if acc.isEmpty then none else some acc
    | c :: cs =>
      if is_digit c then
        preprocess cs (acc.push c) decimal_used
      else if is_thousand_separator c ∧ ¬acc.isEmpty then
        preprocess cs acc decimal_used
      else if is_decimal_point c ∧ ¬decimal_used then
        preprocess cs (acc.push c) true
      else
        if acc.isEmpty then none else some acc

  let parsed_string := 
    match chars with
    | [] => none
    | c :: cs =>
      if c = '-' then
        preprocess cs "-" false
      else
        preprocess chars "" false

  match parsed_string with
  | none => none
  | some parsed_string => 
    match parseFloat parsed_string with
      | none => none
      | some parsed_float => some parsed_float

def parseInput (lines : List String) : List Input :=
  lines.map (fun line => 
    let key := get_first_number line
    ⟨key, line⟩
  )

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
