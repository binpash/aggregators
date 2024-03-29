import utilities
import sys

PAD_LEN = 8 

def s_wc(parallel_res: list[str]):
    build_sum = parallel_res[0] 
    for res in parallel_res[1:]:
        if res == None or res.strip() == "": continue
        build_sum = "".join(str(int(x) + int(y)).rjust(PAD_LEN, ' ') for x, y in zip(build_sum.split(), res.split()))
    return build_sum


def s_combine(output_A, output_B): 
    # utilities reads and process outputs into one array the combiner works on
    try: 
        utilities.write_file(s_wc(utilities.process_input_to_array(output_A, output_B)))
    except: 
        sys.stderr.write("error with combining wc results" + "\n")
        return False

def m_wc(parallel_res, full_files): 
    file_to_count_dict = {}
    for file_output in parallel_res:
        newline_arr=file_output.split("\n") # split each line into its own string 
        for res in newline_arr:
            file_key = utilities.extract_base_file(res.split()[-1])
            if file_key in file_to_count_dict: 
                # file found in dict, add on to current value and append file name
                file_to_count_dict[file_key] = "".join(str(int(old_val) + int(new_val)).rjust(PAD_LEN, ' ') 
                for old_val, new_val in zip(file_to_count_dict[file_key].split()[:-1], res.split()[:-1])) + " " + file_key
            else: 
                file_to_count_dict.setdefault(file_key, res)
    # build output using \n and append total on the end
    return '\n'.join(value for key, value in file_to_count_dict.items() if key != "total") + "\n" + file_to_count_dict["total"]


def m_combine(output_A, output_B, full_files): 
    # utilities reads and process outputs into one array the combiner works on
    try: 
        utilities.write_file(m_wc(utilities.process_input_to_array(output_A, output_B), full_files))
    except: 
        sys.stderr.write("error with combining wc results" + "\n")
        return False