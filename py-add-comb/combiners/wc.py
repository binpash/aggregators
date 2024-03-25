def wc_flags_combine(parallel_res: list[str]):
    """''
    A wc combine that is flexible enough for any wc related flags 
    wc flags include -l, -c, -m, -w or any combinations of them 
        a sample combination such as -wl may return '3 4 hi.txt';  
        instead of the normal wc, which is '3 4 300 hi.txt'
    Based on the shape of wc outputs, this combiners will add up according index and return appropriately

    Parameter:
        parallel-res: an array of parallelized results produced by wc cmd in string 
            formatted by "<line_count> <word_count> <byte/char_count> <input_file_path>" 
            use nothing for input_file_path if using stdout 
    Returns:
        a string result in the format of "count file.txt", where count is all added results
    Raise: valueError a parallelized result is malformatted (not enough args)
    """
    if parallel_res is None or len(parallel_res) == 0:
        return ""

    file_to_count_dict = {}

    for res in parallel_res:
        single_res = res.split(' ')  # split string into array
        if len(single_res) > 4 or len(single_res) == 0:
            raise ValueError("parallel result arrays cannot be null")

        if single_res[-1] in file_to_count_dict:
            # file found in dict, add on to current value, add to total
            for i in range(0, len(single_res)-1):
                file_to_count_dict[single_res[-1]][i] += int(single_res[i])
        else:
            for i in range(0, len(single_res)-1):
                # not found, start new entry, add to total
                single_res[i] = int(single_res[i])
            file_to_count_dict.update({single_res[-1]: single_res})

    # concat all file total results except for total 
    no_total_res = []
    for file, file_add_result in file_to_count_dict.items():
        if (file != "total"):
            no_total_res.append(' '.join(str(val) for val in file_add_result))
    resultStr = '\n'.join(val for val in no_total_res)

    if len(file_to_count_dict) > 1:
        # append the last total if multiple files 
        return resultStr + "\n" + ' '.join(str(val) for val in file_to_count_dict["total"])
    else:
        # just return if wc applied to single files
        return resultStr

def wc_comb_two(output_A:str, output_B:str): 
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
    return wc_flags_combine(parallel_res)

output_A = "30 100 0 hi.txt\n0 0 0 apples.txt\n0 0 0 bye.txt\n30 100 0 total"
output_B = "10 300 1 bye.txt\n20 200 2 hi.txt\n0 0 0 apples.txt\n30 500 3 total"
print(wc_comb_two(output_A, output_B))