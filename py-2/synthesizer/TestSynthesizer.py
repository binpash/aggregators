from synthesizer import *

def example_1():
    expected_output = ["orange", "grape", "banana", "apple"]
    
    annotations = {
        "input_type": "list",
        "output_type": "list",
        # "is_commutative": False,
        # "is_associative": False,
        # "is_idempotent": True,
        # "reduces": True,
        # "preserves_order": False,
        # "is_sorted": True
    }

    partial_outputs = [
        ["orange","banana"],
        ["grape","apple"]
    ]

    comparator = lambda x: -ord(x[0])  # Alphabetical descending sorting based on first letter

    aggregator = synthesize_aggregator(annotations, correct_output=expected_output, partial_outputs=partial_outputs, comparator=comparator)
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        result = aggregator(*partial_outputs)
        print("Aggregator Result:", result)

def example_2():
    expected_output = [1, 2, 3, 4, 5, 6, 7, 8]
    
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

    partial_outputs = [
        [2, 4, 6, 8],
        [1, 3, 5, 7]
    ]

    comparator = lambda x: x  # Numeric ascending sorting

    aggregator = synthesize_aggregator(annotations, correct_output=expected_output, partial_outputs=partial_outputs, comparator=comparator)
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        result = aggregator(*partial_outputs)
        print("Aggregator Result:", result)

def example_3():
    expected_output = ["banana", "orange", "apple", "grape"]
    
    annotations = {
        "input_type": "list",
        "output_type": "list",
        "is_commutative": False,
        "is_associative": True,
        "is_idempotent": False,
        "reduces": False,
        "preserves_order": True,
        "is_sorted": False
    }

    partial_outputs = [
        ["banana", "orange"],
        ["apple", "grape"]
    ]

    aggregator = synthesize_aggregator(annotations, correct_output=expected_output, partial_outputs=partial_outputs, comparator=None)
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        result = aggregator(*partial_outputs)
        print("Aggregator Result:", result)

def example_4():
    expected_output = ["banana", "orange", "apple", "grape"]
    
    annotations = {
        "input_type": "list",
        "output_type": "list",
        "is_commutative": False,
        "is_associative": False,
        "is_idempotent": True,
        "reduces": True,
        "preserves_order": True,
        "is_sorted": False
    }

    partial_outputs = [
        ["banana", "orange", "banana"],
        ["apple", "grape", "orange"]
    ]

    aggregator = synthesize_aggregator(annotations, correct_output=expected_output, partial_outputs=partial_outputs, comparator=None)
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        result = aggregator(*partial_outputs)
        print("Aggregator Result:", result)

def example_5():
    expected_output = 25
    
    annotations = {
        "input_type": "num",
        "output_type": "num",
        "is_commutative": True,
        "is_associative": True,
        "is_idempotent": False,
        "reduces": True
    }

    partial_outputs = [
        10, 15
    ]

    aggregator = synthesize_aggregator(annotations, correct_output=expected_output, partial_outputs=partial_outputs, comparator=None)
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        result = aggregator(*partial_outputs)
        print("Aggregator Result:", result)

def example_6():
    expected_output = ["a", "hi", "cat", "dog", "elephant"]
    
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

    partial_outputs = [
        ["cat", "elephant"],
        ["a", "hi", "dog"]
    ]

    comparator = lambda x: len(x)  # Sort by string length

    aggregator = synthesize_aggregator(annotations, correct_output=expected_output, partial_outputs=partial_outputs, comparator=comparator)
    
    if isinstance(aggregator, str):
        print(aggregator)
    else:
        result = aggregator(*partial_outputs)
        print("Aggregator Result:", result)

if __name__ == "__main__":
    print("Running Example 1:")
    example_1()
    
    print("\nRunning Example 2:")
    example_2()
    
    print("\nRunning Example 3:")
    example_3()
    
    print("\nRunning Example 4:")
    example_4()
    
    print("\nRunning Example 5:")
    example_5()
    
    print("\nRunning Example 6:")
    example_6()
