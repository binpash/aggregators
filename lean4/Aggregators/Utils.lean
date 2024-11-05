-- TODO: Handle errors

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
