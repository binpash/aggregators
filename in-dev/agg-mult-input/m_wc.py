#!/usr/bin/env python3
import utils

PAD_LEN = 8 

def m_combine(parallel_res): 
    file_to_count_dict = {}
    for file_output in parallel_res:
        newline_arr=file_output.split("\n") # split each line into its own string 
        for res in newline_arr:
            file_key = utils.extract_base_file(res.split()[-1])
            if file_key in file_to_count_dict: 
                # file found in dict, add on to current value and append file name
                file_to_count_dict[file_key] = "".join(str(int(old_val) + int(new_val)).rjust(PAD_LEN, ' ') 
                for old_val, new_val in zip(file_to_count_dict[file_key].split()[:-1], res.split()[:-1])) + " " + file_key
            else: 
                file_to_count_dict.setdefault(file_key, res)
    # build output using \n and append total on the end
    return '\n'.join(value for key, value in file_to_count_dict.items() if key != "total") + "\n" + file_to_count_dict["total"]

read = utils.read_all_2()
utils.write_file(m_combine(read)) 