import utilities
import sys

def grep_combine(parallel_res: list[str]):
    if parallel_res is None or len(parallel_res) == 0:
        return ""
    append_together = ""
    for res in parallel_res:
        if res != "":
            append_together = append_together + res + '\n'
    return append_together.strip() 

def combine(output_A, output_B):
    try: 
       utilities.write_file(grep_combine(utilities.process_input_to_array(output_A, output_B)))
    except: 
        sys.stderr.write("error with combining grep results " + '\n')
        return False
