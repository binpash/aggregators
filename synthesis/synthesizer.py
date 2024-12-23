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
        input_type = "Input"
    return CMP_TEMPLATE.format(input_type=input_type, comparison_logic=comparison_logic.strip())

def generate_parse_function(sort_key: str) -> str:
    """Generate parsing function if sort_key requires key extraction."""
    if sort_key == "identity":
        parsing_logic = "lines"
        input_type = "String"
    else:
        parsing_logic = """
        lines.map (fun line => 
          let key := get_first_number line
          ⟨key, line⟩
        )
        """
        input_type = "Input"

    return PARSE_TEMPLATE.format(input_type=input_type, parsing_logic=parsing_logic)

def populate_template(annotations: Dict[str, Any]) -> str:
    """Populate the general Lean template based on annotations."""
    # Stream Initialization
    stream_init = {
        "all": "let streams ← getAllStreams args",
        "first": "let stream ← getFirstStream args",
        "last": "let stream ← getLastStream args",
    }[annotations.get("stream_mode", "all")]

    # Set default helper functions and extra imports
    helper_functions = ""
    extra_imports = ""

    # Include `Input` structure if `sort_key` is used
    sort_key = annotations.get("sort_key", "identity")
    if sort_key != "identity":
        extra_imports += """
structure Input where
  key   : Option Float
  input : String
  deriving Repr

instance : ToString Input where 
  toString : Input → String
  | ⟨_, input⟩ => input
        """
        parse_function = generate_parse_function(sort_key)
        helper_functions += parse_function

    # Processing Logic
    merge_logic = annotations.get("merge_logic", "append")
    processing_logic = ""
    output_logic = ""

    if merge_logic == "sort":
        # Check if reverse sort is required
        order = annotations.get("order", "asc")
        if sort_key == "identity" and order == "desc":
            # Simple reverse sort (no Input structure needed)
            cmp_logic = CMP_TEMPLATE.format(
                input_type="List String",
                comparison_logic="a >= b"
            )
            helper_functions += cmp_logic

            processing_logic = """
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := merge cmp acc lines.toListImpl
      pure acc)
    [] streams
            """
            output_logic = """
  output.forM (fun output => IO.print output)
            """
        else:
            # General sort with custom key or ascending order
            cmp_logic = generate_cmp_logic(sort_key, order)
            helper_functions += cmp_logic

            processing_logic = """
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let inputs := parseInput lines.toListImpl
      let acc := merge cmp acc inputs
      pure acc)
    [] streams
            """
            output_logic = """
  output.forM (fun line => IO.print line)
            """
    elif merge_logic == "sum":
        # Include parseInput for summation
        parse_function = PARSE_TEMPLATE.format(
            input_type="Nat",
            parsing_logic="""
            lines.foldl (fun acc line => acc + line.trim.toNat!) 0
            """.strip()
        )
        helper_functions += parse_function

        processing_logic = """
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let input := parseInput lines.toListImpl
      let acc := sum acc input
      pure acc)
    0 streams
        """
        output_logic = """
  IO.println output
        """
    elif merge_logic == "append":
        processing_logic = """
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFile stream ByteArray.empty
      let acc := concat acc lines
      pure acc)
    ByteArray.empty streams
        """
        output_logic = """
  let stdout ← IO.getStdout
  stdout.write output
        """
    elif merge_logic == "uniq":
        processing_logic = """
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := uniq_agg acc lines.toListImpl
      pure acc)
    [] streams
        """
        output_logic = """
  output.forM (fun line => IO.print line)
        """
    else:
        # Default processing logic (no specific merge logic)
        processing_logic = """
  let output ← List.foldlM 
    (fun acc stream => do
      let lines ← readFileByLine stream
      let acc := acc ++ lines
      pure acc)
    [] streams
        """
        output_logic = """
  output.forM (fun line => IO.print line)
        """

    # Populate Template
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
