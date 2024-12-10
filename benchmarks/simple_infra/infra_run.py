#!/usr/bin/env python3

import argparse
import utils.simple_parse as simple_parse
from execute import execute_par_or_seq
from global_data import GlobalData 

## PARSE ARGS 
parser = argparse.ArgumentParser(description="")
parser.add_argument('--split', '-n', type=int, default=2)
parser.add_argument('--input', '-i', type=str)
parser.add_argument('--script', '-s', type=str)
parser.add_argument('--output', '-o', type=str)
parser.add_argument('-id', type=int)
parser.add_argument('--agg_set', '-agg', type=str)
args, cmds = parser.parse_known_args() 

def run_cmd_loop(global_data: GlobalData) -> str: 
    cmds = simple_parse.parse_pipeline(args.script)   
    print(cmds)
    output_path = ""
    for cmd in cmds:
        global_data.set_cmd(cmd) 
        output_path = execute_par_or_seq(global_data.input, global_data.seq_path, global_data.par_path,
                                                 global_data.split, global_data.split_file_dir, global_data.check_par_output_dir_path, 
                                                 global_data.output_dir_path, global_data.cmd, global_data.agg_set, global_data.debug_log_path) 
        print(output_path)
        global_data.change_input(output_path)
     
    return output_path
    
def run(): 
    globals = GlobalData(args.input, args.script, args.split, args.id, args.agg_set)
    final_output = run_cmd_loop(globals)
    with open(args.output, 'w', newline='\n') as outfile:
        with open(final_output, 'r', encoding='UTF-8-sig', newline='\n') as infile:
            for line in infile:
                outfile.write(line)

run()

        
