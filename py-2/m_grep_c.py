
import utilities

def m_combine(parallel_res: list[str]):
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

read = utilities.read_all()
utilities.write_file(m_combine(read))