#!/usr/bin/env python3
import utils 

def s_combine(parallel_res: list[str]):
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


read = utils.read_all_2()
utils.write_file(s_combine(read)) 
