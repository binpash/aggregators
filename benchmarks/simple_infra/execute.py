def get_output_and_time(byte_str: str): 
    parse_output = byte_str.decode('utf-8').split(",")
    output = parse_output[0]
    time = parse_output[1]
    return (output, time)

def check_use_parallel(cmd: str, agg_set: str):
    if agg_set == "python": 
        return find_agg_py.find(cmd, "../../py-2" + "/")
    else:  
        return find_agg_lean.find(cmd, "../../lean4/.lake/build/bin" + "/")
    

def check_par_exec(par_path: str, seq_path: str) -> bool: 
    rv = subprocess.run(['diff', '-q', par_path, seq_path]).returncode
    if rv >= 0: return True
    
def execute_par(input: str, seq_path: str, par_path: str, split: int, 
                split_file_dir:str, check_par_output_dir_path: str, output_dir_path: str,  
                cmd: str, agg: str, debug_log_path: str) -> str: 
    # Split files and set-up intermediate directory paths. 
    print(split_file_dir)
    split_file_dir_org = f"{split_file_dir}org/"
    split_file_dir_cmd = f"{split_file_dir}cmd/"
    if not os.path.exists(split_file_dir_org): 
        os.makedirs(split_file_dir_org)
    if not os.path.exists(split_file_dir_cmd): 
        os.makedirs(split_file_dir_cmd)
    split_files = simple_split.split_file(input, split, f"{split_file_dir_org}")
    
    # Apply cmd to each partials. 
    partials_after_cmd = []
    for file in split_files: 
        seq_execute_partial = subprocess.check_output([seq_path, file, split_file_dir_cmd, 
                                                       cmd, debug_log_path]) 
        partials_after_cmd.append(get_output_and_time(seq_execute_partial)[0])
    
    # Apply aggregator to combine partials. 
    par_execute = subprocess.check_output([par_path, input, output_dir_path, 
                                           cmd, agg, split_file_dir_cmd, debug_log_path]) 
    seq_execute = subprocess.check_output([seq_path, input, check_par_output_dir_path, 
                                           cmd, debug_log_path])
    par_out, par_time = get_output_and_time(par_execute)
    seq_out, seq_time = get_output_and_time(seq_execute)    
    if (check_par_exec(par_out, seq_out)): 
        return par_out
    else: 
        return seq_out
    
def execute_seq(seq_path: str, input: str, output_dir_path: str,  
                cmd: str, debug_log_path:str) -> str: 
    if not os.path.exists(input): 
        FileExistsError(input + " not found")
        return ""
    seq_execute = subprocess.check_output([seq_path, input, output_dir_path, 
                                           cmd, debug_log_path]) 
    out, time = get_output_and_time(seq_execute) 
    return out 

def execute_par_or_seq(input: str, seq_path: str, par_path: str, split: int, 
                split_file_dir:str, check_par_output_dir_path: str, output_dir_path: str,  
                cmd: str, agg_set: str, debug_log_path: str) -> str: 
    has_valid_agg = check_use_parallel(cmd, agg_set) 
   
    # If aggregator found, use parallel execution. 
    # If parallel execution fails, run sequential instead to not affect next cmd. 
    if has_valid_agg != "": 
        output_path = execute_par(input, seq_path, par_path, split, split_file_dir, 
                                check_par_output_dir_path, output_dir_path,  
                                cmd, has_valid_agg, debug_log_path)
        if output_path is not None: 
            return output_path
        
    # If no aggregator found, use sequential execution. 
    output_path = execute_seq(seq_path, input, output_dir_path, cmd, debug_log_path)
    return output_path

import os, subprocess
import utils.find_agg_py as find_agg_py
import utils.find_agg_lean as find_agg_lean
import utils.simple_split as simple_split
import utils.print as log 