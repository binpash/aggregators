import os
import json
import sys
from typing import Dict, Any
from templates import GENERAL_TEMPLATE, CMP_TEMPLATE, PARSE_TEMPLATE

def generate_cmp_logic(sort_key: str, order: str) -> str:
    """Generate comparison logic."""
    if sort_key == "identity":
        comparison_logic = f"a {'<=' if order == 'asc' else '>='} b"
        input_type = "String"
    else:
        if order == "asc":
            comparison_logic = f"""
  match a.key, b.key with
  | none, none => a.input <= b.input
  | none, some _ => true
  | some _, none => false
  | some a_key, some b_key => 
    if a_key == b_key then
      a.input <= b.input
    else
      a_key < b_key
            """
        else:
            comparison_logic = f"""
  match a.key, b.key with
  | none, none => a.input >= b.input
  | none, some _ => false
  | some _, none => true
  | some a_key, some b_key => 
    if a_key == b_key then
      a.input >= b.input
    else
      a_key > b_key
            """
        input_type = "Input"
    return CMP_TEMPLATE.format(input_type=input_type, comparison_logic=comparison_logic.strip())

def generate_parse_function(sort_key: str, merge_logic: str) -> str:
    """Generate parsing function based on logic."""
    if merge_logic == "sum":
        parsing_logic = """
        lines.foldl (fun acc line => acc + line.trim.toNat!) 0
        """
        input_type = "Nat"
    elif sort_key == "identity":
        parsing_logic = "lines"
        input_type = "String"
    else:
        parsing_logic = """
        lines.map (fun line => 
          let key := get_first_number line
          ⟨key, line⟩
        )
        """
        input_type = "List Input"

    return PARSE_TEMPLATE.format(input_type=input_type, parsing_logic=parsing_logic.strip())

def generate_merge_function(merge_logic: str) -> str:
    """Generate custom merge function if needed."""
    if merge_logic == "uniq_count":
        return """
def uniqCAggregator (xs ys : List Input) : List Input :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs, y :: ys => 
    if x.value == y.value then
      uniqCAggregator (⟨x.key + y.key, x.value⟩ :: xs) ys
    else if x.value < y.value then
      x :: uniqCAggregator xs (y :: ys)
    else
      y :: uniqCAggregator (x :: xs) ys
        """
    return ""

def populate_template(annotations: Dict[str, Any]) -> str:
    """Populate the general Lean template based on annotations."""
    stream_init = {
        "all": "let streams ← getAllStreams args",
        "first": "let stream ← getFirstStream args",
        "last": "let stream ← getLastStream args",
    }[annotations.get("stream_mode", "all")]

    helper_functions = ""
    extra_imports = ""

    sort_key = annotations.get("sort_key", "identity")
    merge_logic = annotations.get("merge_logic", "append")

    if merge_logic == "sum":
        helper_functions += """
def parseInput (lines : List String) : Nat :=
  lines.foldl (fun acc line => acc + line.trim.toNat!) 0
        """
    elif merge_logic == "uniq_count":
        extra_imports += """
structure Input where
  key   : Nat
  value : String
  deriving Repr

instance : ToString Input where 
  toString : Input → String
  | ⟨key, value⟩ => s!" {key} {value}"

        """
        parse_function = """
def parseInput (lines : List String) : List Input :=
  lines.map (fun line =>
    let trimmed := String.trimLeft line
    let key := trimmed.takeWhile (λ c => c.isDigit)
    let count := key.toNat!
    ⟨count, trimmed.drop key.length⟩
  )
        """
        helper_functions += parse_function
    elif sort_key != "identity":
        extra_imports += """
structure Input where
  key   : Option Float
  input : String
  deriving Repr

instance : ToString Input where 
  toString : Input → String
  | ⟨_, input⟩ => input
        """
        parse_function = generate_parse_function(sort_key, merge_logic)
        helper_functions += parse_function

    if merge_logic == "sort":
        cmp_logic = generate_cmp_logic(sort_key, annotations.get("order", "asc"))
        helper_functions += cmp_logic
    elif merge_logic in ["uniq", "uniq_count", "append"]:
        helper_functions += generate_merge_function(merge_logic)

    processing_logic = """
  let output ← List.foldlM 
    (fun acc stream => do
      let {read_logic}
      let acc := {merge_logic_function} acc {final_input}
      pure acc)
    {initial_accumulator} streams
        """.format(
        read_logic="bytes ← readFile stream ByteArray.empty" if annotations["read_mode"] == "bytes" else "lines ← readFileByLine stream",
        final_input="(parseInput lines.toListImpl)" if 'parseInput' in helper_functions else "bytes" if annotations["read_mode"] == "bytes" else "lines.toListImpl",
        merge_logic_function="sum_agg" if merge_logic == "sum" else "concat_agg" if merge_logic == "append" else "uniqCAggregator" if merge_logic == "uniq_count" else merge_logic if merge_logic != "sort" else "merge cmp",
        initial_accumulator="0" if annotations["accumulator_type"] == "int" else "ByteArray.empty" if annotations["accumulator_type"] == "bytes" else "[]",
    )

    output_logic = """
  IO.println output
        """ if annotations.get("output_mode") == "print" else """
  let stdout ← IO.getStdout
  stdout.write output
        """

    return GENERAL_TEMPLATE.format(
        extra_imports=extra_imports.strip(),
        helper_functions=helper_functions.strip(),
        stream_initialization=stream_init.strip(),
        processing_logic=processing_logic.strip(),
        output_logic=output_logic.strip(),
    )

def synthesize_aggregator_to_lean(annotations: Dict[str, Any]) -> str:
    """Generate Lean code for the specified annotations."""
    try:
        return populate_template(annotations)
    except KeyError as e:
        return f"Cannot synthesize aggregator: missing required annotation key {e}"

def generate_lean_file(annotations: Dict[str, Any]):
    lean_code = synthesize_aggregator_to_lean(annotations)
    if "Cannot synthesize" in lean_code:
        print(lean_code)
        return

    # Define the target directory and file
    target_dir = "../lean4"
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
