import json
import sys
from typing import List, Dict, Any
from lean_templates import LEAN_CONCAT_TEMPLATE, LEAN_SORT_TEMPLATE, LEAN_SUM_TEMPLATE
import os

class Function:
    def __init__(self, name: str, operation_type: str, modifiers: Dict[str, bool], input_type: str, output_type: str):
        self.name = name
        self.operation_type = operation_type
        self.modifiers = modifiers
        self.input_type = input_type
        self.output_type = output_type

    def applies_to(self, annotations: Dict[str, Any]) -> bool:
        """Check if this function matches the given annotations."""
        if annotations['operation_type'] != self.operation_type:
            return False
        if annotations['input_type'] != self.input_type or annotations['output_type'] != self.output_type:
            return False
        for mod, value in self.modifiers.items():
            if annotations.get(mod) != value:
                return False
        return True

# Simplified function database
function_database = [
    Function(
        name='concat',
        operation_type='concat',
        modifiers={},
        input_type='list<string>',
        output_type='string'
    ),
    Function(
        name='sort',
        operation_type='sort',
        modifiers={},
        input_type='list<string>',
        output_type='list<string>'
    ),
    Function(
        name='sum',
        operation_type='sum',
        modifiers={"is_numeric": True},
        input_type='list<num>',
        output_type='num'
    )
]

def synthesize_sort_lean(annotations: Dict[str, Any]) -> str:
    """Generate Lean code for sort aggregators."""
    is_numeric = annotations.get("is_numeric", False)
    is_reverse = annotations.get("is_reverse", False)
    key_logic = annotations.get("key_logic", "s.trim")

    # Define input structure
    input_structure = """
structure Input where
  key   : Option Float
  input : String
  deriving Repr

instance : ToString Input where
  toString : Input → String
  | ⟨_, input⟩ => input
""" if is_numeric else """
abbrev Input := String
"""

    # Include helper functions for numeric processing
    helper_functions = """
def is_digit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def is_thousand_separator (c : Char) : Bool :=
  c = ','

def is_decimal_point (c : Char) : Bool :=
  c = '.'
""" if is_numeric else ""

    # Define parse function
    if is_numeric:
        parse_function = f"""
def get_first_number (s : String) : Option Float :=
  let chars := ({key_logic}).toList
  let rec preprocess (chars : List Char) (acc : String) (exponent : Nat) (decimal_used : Bool) : Option Float :=
    match chars with
    | [] =>
      if acc.isEmpty then none
      else some (OfScientific.ofScientific (String.toNat! acc) true exponent)
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
        if acc.isEmpty then none
        else some (OfScientific.ofScientific (String.toNat! acc) true exponent)
  preprocess chars "" 0 false

def parseInput (lines : List String) : List Input :=
  lines.map (fun line =>
    let key := get_first_number line
    ⟨key, line⟩
  )
"""
    else:
        parse_function = """
def parseInput (lines : List String) : List Input :=
  lines
"""

    # Define comparator logic
    if is_numeric:
        comparator_logic = f"""
def cmp (a b : Input) : Bool :=
  match a.key, b.key with
  | none, none => a.input {"<=" if not is_reverse else ">="} b.input
  | none, some _ => {"true" if not is_reverse else "false"}
  | some _, none => {"false" if not is_reverse else "true"}
  | some a_key, some b_key =>
    if a_key == b_key then
      a.input {"<=" if not is_reverse else ">="} b.input
    else
      a_key {"<" if not is_reverse else ">"} b_key
"""
    else:
        comparator_logic = f"""
def cmp (a b : Input) : Bool := a {"<=" if not is_reverse else ">="} b
"""

    # Return complete Lean code
    return LEAN_SORT_TEMPLATE.format(
        input_structure=input_structure,
        helper_functions=helper_functions,
        parse_function=parse_function,
        comparator_logic=comparator_logic,
    )


def synthesize_aggregator_to_lean(annotations: Dict[str, Any]) -> str:
    applicable_functions = [f for f in function_database if f.applies_to(annotations)]
    if not applicable_functions:
        return "Cannot synthesize aggregator: no applicable function found."

    primary_function = applicable_functions[0]
    operation_type = primary_function.operation_type

    if operation_type == 'concat':

        return synthesize_concat_lean(annotations)
    
    elif operation_type == 'sort':

        return synthesize_sort_lean(annotations)
    
    elif operation_type == 'sort' and annotations.get("is_reverse") and not annotations.get("is_numeric"):
        # Special case for `sort r`
        return """
import Synthesis

abbrev Input := String

def parseInput (lines : List String) : List Input :=
  lines

def cmp (a b : Input) : Bool := a >= b

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
    elif operation_type == 'sum':
        return LEAN_SUM_TEMPLATE
    
    return "Operation not supported for synthesis."

def synthesize_concat_lean(annotations: Dict[str, Any]) -> str:
    """Generate Lean code for concat and its variants."""
    if annotations.get("is_first"):
        stream_func = "getFirstStream"
        match_logic = "args"
        stream_function = f"""
def {stream_func} (args : List System.FilePath) : IO IO.FS.Stream :=
  match {match_logic} with
  | [] => throw $ IO.userError "No input files"
  | (arg :: _) => getFileStream arg
"""
        fold_logic = """
let stream ← getFirstStream args
let bytes ← readString stream ByteArray.empty
pure bytes
"""

    elif annotations.get("is_last"):
        stream_func = "getLastStream"
        match_logic = "args.tail"
        stream_function = f"""
def {stream_func} (args : List System.FilePath) : IO IO.FS.Stream :=
  match {match_logic} with
  | [] => throw $ IO.userError "No input files"
  | (arg :: _) => getFileStream arg
"""
        fold_logic = """
let stream ← getLastStream args
let bytes ← readString stream ByteArray.empty
pure bytes
"""

    else:  # General `concat`
        stream_func = "getAllStreams"
        stream_function = f""""""
        fold_logic = """
List.foldlM (fun acc stream => do
    let bytes ← readString stream ByteArray.empty
    let acc := acc.append bytes
    pure acc) ByteArray.empty streams
"""

    # Return the completed Lean template
    return LEAN_CONCAT_TEMPLATE.format(
        stream_func=stream_func,
        stream_function=stream_function,
        fold_logic=fold_logic,
    )



def generate_lean_file(annotations: Dict[str, Any]):
    lean_code = synthesize_aggregator_to_lean(annotations)
    if "Cannot synthesize" in lean_code:
        print(lean_code)
        return

    # Define the target directory and file
    target_dir = "../../lean4"
    filename = "Main.lean"
    full_path = os.path.join(target_dir, filename)

    # Ensure the target directory exists
    os.makedirs(target_dir, exist_ok=True)

    # Write the Lean file
    with open(full_path, "w") as lean_file:
        lean_file.write(lean_code)
    print(f"Lean file '{full_path}' created with synthesized aggregator.")

def load_annotations(filename: str) -> Dict[str, Any]:
    try:
        with open(filename, "r") as json_file:
            return json.load(json_file)
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        return {}
    except json.JSONDecodeError:
        print(f"Error: File '{filename}' is not a valid JSON file.")
        return {}

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 synthesizer.py <annotations.json>")
        sys.exit(1)

    annotations_file = sys.argv[1]
    annotations = load_annotations(annotations_file)
    if annotations:
        generate_lean_file(annotations)
