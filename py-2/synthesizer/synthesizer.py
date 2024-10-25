from itertools import permutations
from typing import List, Dict, Callable, Any, Union

class Function:
    def __init__(self, name: str, func: Callable, 
                 function_properties: Dict[str, bool], 
                 output_properties: Dict[str, bool], 
                 input_type: str, output_type: str):
        self.name = name
        self.func = func
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


function_database = [
    Function(
        name='merge_sort',
        function_properties={
            "is_idempotent": True
        },
        output_properties={
            "is_sorted": True,
        },
        input_type='list',
        output_type='list'
    ),
    Function(
        name='unique',
        function_properties={
            "is_idempotent": True
        },
        output_properties={
            "reduces": True
        },
        input_type='list',
        output_type='list'
    ),
    Function(
        name='cat',
        function_properties={
            "is_commutative": False,
        },
        output_properties={},
        input_type='list',
        output_type='list'
    ),
    Function(
        name='sum',
        function_properties={
            "is_commutative": True,
        },
        output_properties={
        },
        input_type='num',
        output_type='num'
    ),
]


def synthesize_aggregator_to_lean(annotations: Dict[str, Any], comparator: str = "a.key <= b.key") -> Union[str, str]:    
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

def example_2():    
    annotations = {
        "input_type": "list",
        "output_type": "list",
        "is_idempotent": True,
        "reduces": False,
        "is_sorted": True
    }
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        print("Lean Aggregator:",synthesize_aggregator_to_lean(annotations, comparator="a.key <= b.key"))

if __name__ == "__main__":
    print("\nRunning Example 2:")
    example_2()
