import subprocess
from subprocess import CompletedProcess

binary_path = "./wc_rust"
input_type = str
str_tests = ["", "a\n", "a\na"]

def run_process(input) -> CompletedProcess:
    return subprocess.run(
        [binary_path, input],
        # input=input,
        capture_output=True,
        text=True,
    )

def test_add():
    test = "hello world"
    seq_process = run_process(test)

    if seq_process.returncode != 0: return False
    try: seq_output = int(seq_process.stdout)
    except: return False
    print(seq_output)

    test_lines = test.split("\n")
    par_processes = map(lambda x: run_process(x), test_lines)

    par_output = 0
    for par_process in par_processes: 
        if par_process.returncode != 0: return False
        try: par_output += int(par_process.stdout)
        except: return False

    print(par_output)
    if par_output != seq_output: return False

    return True

print(test_add())
