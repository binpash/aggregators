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
