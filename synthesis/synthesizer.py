import json
import sys
from itertools import permutations
from typing import List, Dict, Callable, Any, Union

class Function:
    def __init__(self, name: str, 
                 function_properties: Dict[str, bool], 
                 output_properties: Dict[str, bool], 
                 input_type: str, output_type: str):
        self.name = name
        self.function_properties = function_properties
        self.output_properties = output_properties
        self.input_type = input_type
        self.output_type = output_type

    def applies_to(self, annotations: Dict[str, Any]) -> bool:
        """Check if this function matches the given annotations."""
        if annotations['input_type'] != self.input_type or annotations['output_type'] != self.output_type:
            return False
        for prop in self.function_properties:
            if prop in annotations and annotations[prop] != self.function_properties[prop]:
                return False
        for prop in self.output_properties:
            if prop in annotations and annotations[prop] != self.output_properties[prop]:
                return False
        return True

# Function database for possible aggregators
function_database = [
    Function(
        name='merge_sort',
        function_properties={"is_idempotent": True},
        output_properties={"is_sorted": True},
        input_type='list',
        output_type='list'
    ),
    Function(
        name='unique',
        function_properties={"is_idempotent": True},
        output_properties={"reduces": True},
        input_type='list',
        output_type='list'
    ),
    Function(
        name='cat',
        function_properties={"is_commutative": False},
        output_properties={},
        input_type='list',
        output_type='list'
    ),
    Function(
        name='sum',
        function_properties={"is_commutative": True},
        output_properties={},
        input_type='num',
        output_type='num'
    ),
]

def synthesize_aggregator_to_lean(annotations: Dict[str, Any], comparator: str = "a.key <= b.key") -> str:    
    essential_functions = [f for f in function_database if f.applies_to(annotations) and f.name in ['merge_sort', 'cat', 'sum']]
    if not essential_functions:
        return "Cannot synthesize aggregator: no applicable 'merge_sort', 'cat', or 'sum' function found."
    
    primary_function = essential_functions[0]
    lean_expression = ""

    if primary_function.name == 'merge_sort':
        lean_expression = f"merge (fun a b => {comparator})"
    elif primary_function.name == 'cat':
        lean_expression = "cat"
    elif primary_function.name == 'sum':
        lean_expression = "sum"

    # Add any additional applicable functions
    applicable_functions =  [f for f in function_database if f.applies_to(annotations) and f.name not in ['merge_sort', 'cat', 'sum']]
    for function_permutation in permutations(applicable_functions):
        if primary_function not in function_permutation:
            function_permutation = (primary_function,) + function_permutation
        
        for func in function_permutation:
            if func != primary_function:
                if func.name == 'unique':
                    lean_expression += " ∘ unique" 
                elif func.name == 'merge_sort':
                    lean_expression += f" ∘ merge (fun a b => {comparator})"

    return lean_expression

def generate_lean_file(annotations: Dict[str, Any], comparator: str = "a.key <= b.key"):
    lean_code = synthesize_aggregator_to_lean(annotations, comparator=comparator)
    lean_file_content = f"""
import Aggregators

def main (args : List String) : IO UInt32 := do
let args : List System.FilePath := List.map (fun arg ↦ ⟨arg⟩) args
let streams ← getAllStreams args

let output ← List.foldlM (fun acc stream => do
    let lines ← readFile stream []
    let inputs := parseInput lines
    let acc := {lean_code} acc inputs
    pure acc) 
    [] streams

output.forM (fun output => IO.print output)
return 0
        """
    # Writing everything to a single file
    with open("GeneratedAggregator.lean", "w") as lean_file:
        lean_file.write(lean_file_content)
    print("Lean file 'GeneratedAggregator.lean' created with synthesized aggregator.")

def load_annotations(filename: str) -> Dict[str, Any]:
    """Load annotations from a JSON file."""
    try:
        with open(filename, "r") as json_file:
            annotations = json.load(json_file)
            return annotations
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
        print("Lean Aggregator:", synthesize_aggregator_to_lean(annotations, comparator="a.key <= b.key"))
        generate_lean_file(annotations, comparator="a.key <= b.key")
