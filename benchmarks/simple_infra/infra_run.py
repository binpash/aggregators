#!/usr/bin/env python3

import argparse
import utils.simple_parse as simple_parse
from execute import execute_par_or_seq
import globals

## PARSE ARGS 
parser = argparse.ArgumentParser(description="")
parser.add_argument('--split', '-n', type=int, default=2)
parser.add_argument('--input', '-i', type=str)
parser.add_argument('--script', '-s', type=str)
parser.add_argument('--output', '-o', type=str)
parser.add_argument('-id', type=int)
parser.add_argument('--agg_set', '-agg', type=str)
args, cmds = parser.parse_known_args() 

def run_cmd_loop() -> str: 
    cmds = simple_parse.parse_pipeline(args.script)   
    print(cmds)
    output_path = ""
    for cmd in cmds:
        globals.set_cmd(cmd) 
        output_path = execute_par_or_seq(globals.input, globals.seq_path, globals.par_path,
                                                 globals.split, globals.split_file_dir, globals.check_par_output_dir_path, 
                                                 globals.output_dir_path, globals.cmd, globals.agg_set, globals.debug_log_path) 
        print(output_path)
        globals.change_input(output_path)
     
    return output_path
    
def run(): 
    globals.setup_global_files(args.input, args.script, args.split, args.id, args.agg_set)
    globals.setup_dir()
    final_output = run_cmd_loop()
    with open(args.output, 'w', newline='\n') as outfile:
        with open(final_output, 'r', encoding='UTF-8-sig', newline='\n') as infile:
            for line in infile:
                outfile.write(line)

run()

        
