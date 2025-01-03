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

# New property tests
def check_base_case(script_path):
    return run_shell_function(script_path, "") == ""

def check_length_equality(input_str, script_path):
    return len(input_str) == len(run_shell_function(script_path, input_str))

def check_length_less_or_equal(input_str, script_path):
    return len(run_shell_function(script_path, input_str)) <= len(input_str)

def check_membership(input_str, script_path):
    output = run_shell_function(script_path, input_str)
    return all(char in input_str for char in output)

def check_idempotence(input_str, script_path):
    output = run_shell_function(script_path, input_str)
    return output == run_shell_function(script_path, output)

def check_ordering(input_str, script_path, larger_str):
    return run_shell_function(script_path, input_str) <= run_shell_function(script_path, larger_str)

def check_equality(input_str, script_path):
    return run_shell_function(script_path, input_str) == run_shell_function(script_path, input_str)

# Load inputs from text files
def load_inputs_from_file(file_path):
    """Load inputs from a text file, where each line is a separate input."""
    if not os.path.exists(file_path):
        raise FileNotFoundError(f"The input file {file_path} does not exist")
    with open(file_path, 'r') as file:
        return [line.strip() for line in file if line.strip()]

# Test new properties
if __name__ == "__main__":
    script_path = "alphabetic_sort.sh"  
    input_file = "testInputs/input1.txt"  
    output_file = "results.txt"

    if not os.path.exists(script_path):
        raise FileNotFoundError(f"The script file {script_path} does not exist")

    inputs = load_inputs_from_file(input_file)

    with open(output_file, 'w') as outfile:
        for input_str in inputs:
            outfile.write(f"Testing input: {input_str}\n")

            if check_length_equality(input_str, script_path):
                outfile.write("PASS: Length equality\n")
            else:
                outfile.write("FAIL: Length equality\n")

            if check_length_less_or_equal(input_str, script_path):
                outfile.write("PASS: Length less or equal\n")
            else:
                outfile.write("FAIL: Length less or equal\n")

            if check_membership(input_str, script_path):
                outfile.write("PASS: Membership\n")
            else:
                outfile.write("FAIL: Membership\n")

            if check_idempotence(input_str, script_path):
                outfile.write("PASS: Idempotence\n")
            else:
                outfile.write("FAIL: Idempotence\n")

            for larger_str in inputs:
                if input_str in larger_str:
                    if check_ordering(input_str, script_path, larger_str):
                        outfile.write(f"PASS: Ordering between {input_str} and {larger_str}\n")
                    else:
                        outfile.write(f"FAIL: Ordering between {input_str} and {larger_str}\n")

            if check_equality(input_str, script_path):
                outfile.write("PASS: Equality\n")
            else:
                outfile.write("FAIL: Equality\n")
