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
        return True

# Database of functions
function_database = [
    Function(
        name='sort',
        func=lambda lst: sorted(lst),
        function_properties={
            "is_associative": False,
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
        func=lambda lst: list(dict.fromkeys(lst)),  # Maintains order
        function_properties={
            "is_associative": False,
            "is_commutative": False,
            "is_idempotent": True
        },
        output_properties={
            "is_sorted": False,
            "reduces": True
        },
        input_type='list',
        output_type='list'
    ),
    Function(
        name='cat',
        func=lambda lst1, lst2: lst1 + lst2,
        function_properties={
            "is_associative": True,
            "is_commutative": False,
        },
        output_properties={},
        input_type='list',
        output_type='list'
    ),
    Function(
        name='sum',
        func=lambda num1, num2: num1 + num2,
        function_properties={
            "is_associative": True,
            "is_commutative": True,
            "is_idempotent": False
        },
        output_properties={
            "is_sorted": False,
            "reduces": False
        },
        input_type='num',
        output_type='num'
    ),
]

# Function to synthesize an aggregator based on annotations and real partial outputs
def synthesize_aggregator(annotations: Dict[str, Any], correct_output: Any, partial_outputs: List[Any]) -> Union[Callable, str]:
    applicable_functions = [f for f in function_database if f.applies_to(annotations)]

    # Ensure we have at least one 'add' or 'cat' function
    essential_function = next((f for f in applicable_functions if f.name in ['cat', 'sum']), None)
    if not essential_function:
        return "Cannot synthesize aggregator: no applicable 'add' or 'cat' function found."

    # Iterate over all permutations of applicable functions
    for function_permutation in permutations(applicable_functions):
        def aggregator(*partial_outputs):
            # Start by applying the essential function
            if essential_function.func.__code__.co_argcount == 2:
                result = essential_function.func(partial_outputs[0], partial_outputs[1])
            else:
                result = essential_function.func(partial_outputs[0])

            # Apply the remaining functions in the specified order
            for func in function_permutation:
                if func != essential_function:
                    result = func.func(result)

            return result

        # Test the aggregator with actual partial outputs passed to the function
        test_output = aggregator(*partial_outputs)

        # Check if the generated output matches the expected output
        if test_output == correct_output:
            return aggregator

    return "No combination of functions produced the correct output."

# Example usage
if __name__ == "__main__":
    expected_output = [1, 2, 3, 4, 5]
    
    annotations = {
        "input_type": "list",
        "output_type": "list",
        "is_commutative": False,
        "is_associative": False,
        "is_idempotent": True,
        "reduces": True,
        "preserves_order": False,
        "is_sorted": True
    }

    # Assume these are the partial outputs produced by parallel processes
    partial_outputs = [
        [1, 3, 5],
        [2, 3, 4]
    ]

    # Now we pass the partial_outputs to synthesize_aggregator
    aggregator = synthesize_aggregator(annotations, correct_output=expected_output, partial_outputs=partial_outputs)
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        result = aggregator(*partial_outputs)
        print("Aggregator Result:", result)
