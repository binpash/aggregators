#!/usr/bin/env python3

import argparse, os, subprocess
import execution.simple_split
import execution, simple_parse, find_agg_lean, find_agg_py

## PARSE ARGS 
parser = argparse.ArgumentParser(description="")

## FLAGS
parser.add_argument('--split', '-n', type=int, default=2)
parser.add_argument('--input', '-i', type=str)
parser.add_argument('--script', '-s', type=str)
parser.add_argument('-id', type=int)
parser.add_argument('--agg_set', '-agg', type=str)
args, cmds = parser.parse_known_args()

script_name = os.path.splitext(args.script)[0]
input_name = os.path.splitext(os.path.basename(args.input))[0]
inter_dir_path = "inputs-s-" + str(args.id)
output_dir_path = "outputs-temp/agg/"
par_path = "execution/test-par-driver.sh"
seq_path = "execution/test_seq-driver.sh"
debug_log_path = output_dir_path + "debug.log"

def setup_dir(): 
    if not os.path.exists(output_dir_path): 
        os.makedirs(output_dir_path)

    if not os.path.exists(inter_dir_path):
        os.makedirs(inter_dir_path) 

def check_use_parallel(cmd: str):
    if args.agg_set == "python": 
        return find_agg_py.find(cmd, "../../py-2" + "/")
    else: 
        return find_agg_lean.find(cmd, "../../lean4/.lake/build/bin" + "/")

def execute_par() -> int: 
    split_file_prefix = f"{inter_dir_path}/{input_name}"
    print(split_file_prefix)
    split_files = execution.simple_split.split_file(args.input, args.split, split_file_prefix)
    print(split_files)
    return 0
    # return subprocess.call(par_path)
    
def execute_seq() -> int: 
    seq_execute = subprocess.check_output(seq_path, args.input, output_dir_path, cmd, debug_log_path) 
    rv = subprocess.check_call(seq_execute) 
    return rv
    

def execute(cmd: str) -> int: 
    has_valid_agg = check_use_parallel(cmd) 
    print(has_valid_agg)
   
    if has_valid_agg != "": 
        if execute_par() == 0: 
            return 0
    
    # use par if 1) no agg. found, 2) parallel execution errors
    rv = execute_seq()
    return rv

def run(): 
    setup_dir()
    cmds = simple_parse.parse_pipeline(args.script)
    
    print(cmds)
    for cmd in cmds: 
        execute(cmd)
    
run()

        
