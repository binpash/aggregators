# Lean templates for different aggregators

LEAN_CONCAT_TEMPLATE = """
import Synthesis

abbrev Input := String

{stream_function}

def main (args : List String) : IO UInt32 := do
  let args : List System.FilePath := args.map (fun arg => ⟨arg⟩)  -- Ensure correct type
  let streams ← {stream_func} args
  let output ← {fold_logic}

  let stdout ← IO.getStdout
  stdout.write output
  return 0
"""



LEAN_SORT_TEMPLATE = """
import Synthesis

{input_structure}

{helper_functions}

{parse_function}

{comparator_logic}

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
"""



LEAN_SUM_TEMPLATE = """
abbrev Input := Nat

def parseInput (lines : List String) : Input :=
    lines.foldl (fun acc line => acc + line.trim.toNat!) 0

def main (args : List String) : IO UInt32 := do
    let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
    let streams ← getAllStreams args

    let output ← List.foldlM (fun acc stream => do
        let lines ← readFile stream []
        let input := parseInput lines
        let acc := acc + input
        pure acc) 
        (0 : Input) streams

    IO.println output
    return 0
"""
