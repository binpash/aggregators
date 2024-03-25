import heapq

# Simple combine includes combiner for standard command outputs without any flags


def wc_combine(parallel_res: list[str]):
    """
    Combiner Function for command wc 

    Parameter:
        parallel-res: an array of parallelized results produced by wc cmd in string 
            formatted by "<line_count> <word_count> <byte/char_count> <input_file_path>" 
            use nothing for input_file_path if using stdout 
    Returns:
        a string result; 
        if only one file was present the total count line will not be appended; 
        if multiple file present, append total count line 
    Raise: valueError a parallelized result is malformatted (not enough args)
    """
    if parallel_res is None or len(parallel_res) == 0:
        return ""

    file_to_count_dict = {}
    total_count = [0, 0, 0, "total"]

    for res in parallel_res:
        single_res = res.split(' ')  # split string into array
        if len(single_res) != 4:
            raise ValueError("parallel result arrays cannot be null")
        if single_res[3] in file_to_count_dict:
            # found in dict, add on to current value, add to total
            for i in range(3):
                file_to_count_dict[single_res[3]][i] += int(single_res[i])
                total_count[i] += int(single_res[i])
        else:
            for i in range(3):
                # not found, start new entry, add to total
                single_res[i] = int(single_res[i])
                total_count[i] += int(single_res[i])
            file_to_count_dict.update({single_res[3]: single_res})

    # concat each dict entry into string
    for file, file_add_result in file_to_count_dict.items():
        file_to_count_dict[file] = ' '.join(str(val)
                                            for val in file_add_result)
    # concat all dict entry together
    resultStr = '\n'.join(file_to_count_dict.values())
    # decide if to append on total result
    return resultStr + "\n" + ' '.join(str(val) for val in total_count) if len(file_to_count_dict.values()) > 1 else resultStr


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


def sort_combine(parallel_res: list[str], isSmToBig: bool):
    """
    Combiner function for sort 
    Takes all parallelized result and sort them using a minHeap 

    Parameter:
        parallel-res: an array of parallelized results where each stores lines 
            after called sort on that file separated with newline character 
        isSmToBig: true for sorting the combined result from small to big; false otherwise 
            _Note: potentially for the -r flag? 
    Returns:
        a string, sorted result separated by newline combining all parallelized results
    """
    if parallel_res is None or len(parallel_res) == 0:
        return ""

    # put everything in the heap
    sort = []
    for res in parallel_res:
        str_arr = res.split('\n')
        for val in str_arr:
            sort.append(val)

    # sort
    heapq.heapify(sort)

    # join all sort results together & reverse them if isSmToBig is false
    return '\n'.join([heapq.heappop(sort) for _ in range(len(sort))]
                     if isSmToBig else
                     reversed([heapq.heappop(sort) for _ in range(len(sort))]))
