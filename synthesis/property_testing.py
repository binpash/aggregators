import subprocess
import os

def run_shell_function(script_path, input_str):
    """Run the shell script function with the given input and return its output."""
    result = subprocess.run(
        ["bash", script_path],
        input=input_str,
        text=True,
        capture_output=True,
    )
    return result.stdout.strip()

# Property testing
def check_length_equal(input_str, output_str):
    return len(output_str) == len(input_str)

def check_length_smaller_or_equal(input_str, output_str):
    return len(output_str) <= len(input_str)

def check_output_subset_of_input(input_str, output_str):
    return all(char in input_str for char in output_str)

def check_subset_preservation(script_path, input_a, input_b):
    if set(input_b).issubset(set(input_a)):
        output_a = run_shell_function(script_path, input_a)
        output_b = run_shell_function(script_path, input_b)
        return len(output_b) <= len(output_a)
    return True

def check_sum_property(input_list, script_path):
    combined_input = "".join(input_list)
    combined_output = run_shell_function(script_path, combined_input)
    total_output_length = sum(len(run_shell_function(script_path, inp)) for inp in input_list)
    return len(combined_output) <= total_output_length

# Load inputs from text files
def load_inputs_from_file(file_path):
    """Load inputs from a text file, where each line is a separate input."""
    if not os.path.exists(file_path):
        raise FileNotFoundError(f"The input file {file_path} does not exist")
    with open(file_path, 'r') as file:
        return [line.strip() for line in file if line.strip()]

# Test properties on inputs from files
def test_properties_from_file(script_path, input_file):
    inputs = load_inputs_from_file(input_file)
    for input_str in inputs:
        output = run_shell_function(script_path, input_str)
        if check_length_equal(input_str, output):
            print(f"PASS: Length equal for input: {input_str}")
        else:
            print(f"FAIL: Length not equal for input: {input_str}")

        if check_length_smaller_or_equal(input_str, output):
            print(f"PASS: Length smaller or equal for input: {input_str}")
        else:
            print(f"FAIL: Length exceeds input for input: {input_str}")

        if check_output_subset_of_input(input_str, output):
            print(f"PASS: Output is a subset of input for input: {input_str}")
        else:
            print(f"FAIL: Output is not a subset of input for input: {input_str}")

def test_subset_preservation_from_file(script_path, input_file_a, input_file_b):
    inputs_a = load_inputs_from_file(input_file_a)
    inputs_b = load_inputs_from_file(input_file_b)
    for input_a, input_b in zip(inputs_a, inputs_b):
        if check_subset_preservation(script_path, input_a, input_b):
            print(f"PASS: Subset property preserved for inputs: {input_a}, {input_b}")
        else:
            print(f"FAIL: Subset property violated for inputs: {input_a}, {input_b}")

def test_sum_property_from_file(script_path, input_list_file):
    input_list = load_inputs_from_file(input_list_file)
    if check_sum_property(input_list, script_path):
        print("PASS: Sum property preserved for inputs from file")
    else:
        print("FAIL: Sum property violated for inputs from file")
if __name__ == "__main__":
    script_path = "alphabetic_sort.sh"  
    input_file = "testInputs/input1.txt"  
    input_file_a = "testInputs/input2.txt"  
    input_file_b = "testInputs/input3.txt" 
    input_list_file = "testInputs/input4.txt" 

    if not os.path.exists(script_path):
        raise FileNotFoundError(f"The script file {script_path} does not exist")

    # Run the tests
    test_properties_from_file(script_path, input_file)
    test_subset_preservation_from_file(script_path, input_file_a, input_file_b)
    test_sum_property_from_file(script_path, input_list_file)
