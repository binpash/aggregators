from grep_meta import Grep_Par_Output

def grep_c(parallel_res: list[Grep_Par_Output]):
    '''
    Combiner for grep with -c count flag 

    Params: 
        parallel_res: a list of Grep_Par_Output where each holds an ouptut 
            of a block with the block ordering and the command output 

    Returns: 
         a string result of all grep -c results after adding together and separated by newline 
    '''
    file_to_count = {}
    for grep_output in parallel_res:
        for line in grep_output.parallel_output:
            grep_output_to_arr = line.split(":")
            # 1 file only: 3
            # 2+ files: text.txt:3
            count_idx = 0 if len(grep_output_to_arr) <= 1 else 1
            file_path = grep_output_to_arr[0] if len(
                grep_output_to_arr) > 1 else "file_name_substitute"

            # build count map
            if file_path in file_to_count:
                # file found in dict, add on to current value
                file_to_count[file_path] += int(
                    grep_output_to_arr[count_idx])
            else:
                # not found, start new entry
                file_to_count.update(
                    {file_path: int(grep_output_to_arr[count_idx])})

    # build answers to file:count if there is more than 1 file
    if len(file_to_count) > 1:
        # build all dict entry into one string (append total last)
        no_total_res = []
        for file, file_add_result in file_to_count.items():
            if (file != "total"):
                no_total_res.append(file + ':' + str(file_add_result))
        # concat all dict entry together
        resultStr = '\n'.join(no_total_res)
        return resultStr + "\n" + "total:" + str(file_to_count["total"])
    else:
        return " ".join(str(count) for count in file_to_count.values())

def grep_c_comb_two(output_A:str, output_B:str): 
    parallel_res = []
    if (output_B == None or output_B.strip() == "") and (output_A == None or output_A.strip() == ""):
        raise ValueError('both input cannot be nothing')
    
    if output_A == None or output_A.strip() == "": 
        parallel_res.append(Grep_Par_Output(output_B.split("\n"), 1))
    elif output_B == None or output_B.strip() == "":
        parallel_res.append(Grep_Par_Output(output_A.split("\n"), 1))
    else: 
        parallel_res.append(Grep_Par_Output(output_A.split("\n"), 1))
        parallel_res.append(Grep_Par_Output(output_B.split("\n"), 2))
    return grep_c(parallel_res)

# Run 
output_A = "hi.txt:2\nbye.txt:10\ntotal:12"
output_B = "hi.txt:60\nbye.txt:400\napples.txt:10\ntotal:470"
output_A2 = "3"
output_B2 = "4"
print(grep_c_comb_two(output_A2, output_B2))