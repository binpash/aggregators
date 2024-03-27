from grep_meta import Grep_Par_Output
import utilities, sys

def grep_c(parallel_res: list[str]):
    '''
    Combiner for grep with -c count flag 

    Params: 
        parallel_res: a list of Grep_Par_Output where each holds an ouptut 
            of a block with the block ordering and the command output 

    Returns: 
         a string result of all grep -c results after adding together and separated by newline 
    '''
    file_to_count = {}
    for line in parallel_res:
        grep_output_to_arr = line.split(":")
        # 1 file only: 3
        # 2+ files: text.txt:3
        count_idx = 0 if len(grep_output_to_arr) <= 1 else 1
        file_path = grep_output_to_arr[0] if len(
            grep_output_to_arr) > 1 else "file_name_substitute"

        # build count map
        file_to_count.setdefault(file_path, 0)
        file_to_count[file_path] += int(grep_output_to_arr[count_idx])

    # build answers to file:count if there is more than 1 file
    if len(file_to_count) > 1:
        return '\n'.join(str(value) for key, value in file_to_count.items() if key != "total") + "\n" + file_to_count["total"]
    else:
        return " ".join(str(count) for count in file_to_count.values())

def combine(output_A, output_B): 
    try:
        processed_args = utilities.process_input_to_array(output_A, output_B)
        utilities.write_file(grep_c(processed_args)) 
    except: 
        sys.stderr.write("error with combining grep results " + '\n')
        return False

