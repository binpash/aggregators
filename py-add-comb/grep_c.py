import utilities, sys

def s_grep_c(parallel_res: list[str]):
    '''
    Combiner for grep with -c count flag 

    Params: 
        parallel_res: a list of Grep_Par_Output where each holds an ouptut 
            of a block with the block ordering and the command output 

    Returns: 
         a string result of all grep -c results after adding together and separated by newline 
    '''
    total = 0 
    for line in parallel_res: total += int(line)
    return str(total)

def s_combine(output_A, output_B): 
    try:
        processed_args = utilities.process_input_to_array(output_A, output_B)
        utilities.write_file(s_grep_c(processed_args)) 
    except: 
        sys.stderr.write("error with combining grep -c results " + '\n')
        return False


def m_grep_c(parallel_res: list[str], full_files):
    '''
    Combiner for grep with -c count flag 

    Params: 
        parallel_res: a list of Grep_Par_Output where each holds an ouptut 
            of a block with the block ordering and the command output 

    Returns: 
         a string result of all grep -c results after adding together and separated by newline 
    '''
    lines = []
    for line in parallel_res: lines.extend(line.split('\n'))
    file_to_count = {}
    for line in lines: 
        grep_output_to_arr = line.split(":")
        base_file = utilities.extract_base_file(grep_output_to_arr[0])
        # build count map
        file_to_count.setdefault(base_file, 0)
        file_to_count[base_file] += int(grep_output_to_arr[1])

    # build answers to file:count if there is more than 1 file
    return '\n'.join(key+":"+str(value) for key, value in file_to_count.items())

def m_combine(output_A, output_B, full_files): 
    try:
        processed_args = utilities.process_input_to_array(output_A, output_B)
        utilities.write_file(m_grep_c(processed_args, full_files)) 
    except: 
        sys.stderr.write("error with combining grep -c results " + '\n')
        return False

