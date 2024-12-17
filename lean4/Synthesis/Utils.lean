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

/-- Consumes a list of file paths and returns an array of streams. -/
def getAllStreams (args: List String) : IO (List IO.FS.Stream) := do
  List.mapM (fun arg ↦ getFileStream ⟨arg⟩) args

/-- Consumes a list of file paths and returns the first stream. -/
def getFirstStream (args : List String) : IO IO.FS.Stream :=
  match args with
  | [] => throw $ IO.userError "No input files"
  | (arg :: _) => getFileStream arg

/-- Consumes a list of file paths and returns the last stream. -/
def getLastStream (args : List String) : IO IO.FS.Stream :=
  match args with
  | [] => throw $ IO.userError "No input files"
  | (x :: []) => getFileStream x
  | (_ :: xs) => getLastStream xs

/-- Reads from the stream and writes to stdout until the stream is empty. -/
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

/-- Reads from the stream and returns a ByteArray. -/
partial def readFile (stream : IO.FS.Stream) (buf : ByteArray) : IO ByteArray := do
  let str ← stream.read bufsize
  if str.isEmpty then
    pure buf
  else
    let buf := buf ++ str
    readFile stream buf

/-- Reads from a stream and returns an array of lines.-/
partial def readFileByLine (stream : IO.FS.Stream) : IO (Array String) := do
  let mut ret : Array String := #[]
  let mut line : String ← stream.getLine
  while ! line.isEmpty do
    ret := ret.push line
    line ← stream.getLine
  return ret

/-- Reads from the array of streams and returns an array of all lines. -/
partial def readAllByLine (streams : Array IO.FS.Stream) (buf : Array String) : IO (Array String) := do
  streams.foldlM (fun buf stream => do
    let buf' ← readFileByLine stream
    pure (buf ++ buf')
  ) buf


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

