import utilities
import sys

PAD_LEN = 8 

def is_int(value:str):
    try: 
        int(value)
        return True 
    except:
        return False

def wc_flags_combine(parallel_res: list[str]):
    # check if wc applied to single file or multiple files
    is_single_file = is_int(parallel_res[0].split()[-1]) 
    
    if is_single_file:
        build_sum = parallel_res[0] 
        for res in parallel_res[1:]:
            if res == None or res.strip() == "": continue
            build_sum = "".join(str(int(x) + int(y)).rjust(PAD_LEN, ' ') for x, y in zip(build_sum.split(), res.split()))
        return build_sum
    else: 
        file_to_count_dict = {}
        for file_output in parallel_res:
            newline_arr=file_output.split("\n") # split each line into its own string 
            for res in newline_arr:
                file_key = res.split()[-1]
                file_to_count_dict.setdefault(file_key, res)
                # file found in dict, add on to current value and append file name
                file_to_count_dict[file_key] = "".join(str(int(old_val) + int(new_val)).rjust(PAD_LEN, ' ') 
                for old_val, new_val in zip(file_to_count_dict[file_key].split()[:-1], res.split()[:-1])) + " " + file_key
        # build output using \n and append total on the end
        return '\n'.join(value for key, value in file_to_count_dict.items() if key != "total") + "\n" + file_to_count_dict["total"]

def combine(output_A, output_B): 
    # utilities reads and process outputs into one array the combiner works on
    try: 
        utilities.write_file(wc_flags_combine(utilities.process_input_to_array(output_A, output_B)))
    except: 
        sys.stderr.write("error with combining wc results" + "\n")
        return False