def grep_combine(parallel_res: list[str]):
    '''
    Combiner function for grep
    Concat results after command ran in parallel together 

    Parameter:
        parallel-res: an array of parallelized results where each stores lines of grep 
            result separated with newline character 
    Returns:
        a string result of all grep results concat together and separated by newline 
    '''
    if parallel_res is None or len(parallel_res) == 0:
        return ""
    append_together = ""
    for res in parallel_res:
        if res != "":
            append_together = append_together + res + '\n'
    return append_together.rstrip()  # strip away the last '\n'

def grep_comb_two(output_A:str, output_B:str): 
    parallel_res = []
    if (output_B == None or output_B.strip() == "") and (output_A == None or output_A.strip() == ""):
        raise ValueError('both input cannot be nothing')
    
    if output_A == None or output_A.strip() == "": 
        parallel_res.extend(output_B.split("\n"))
    elif output_B == None or output_B.strip() == "":
        parallel_res.extend(output_A.split("\n"))
    else: 
        parallel_res.extend(output_A.split("\n"))
        parallel_res.extend(output_B.split("\n"))
    return grep_combine(parallel_res)

# Run 
output_A = "hi 1\nhi 2\nhi 3"
output_B = "hi 1\nhi 2\nhi 3"
print(grep_comb_two(output_A, output_B))