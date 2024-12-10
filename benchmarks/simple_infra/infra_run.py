#!/usr/bin/env python3

import argparse
import utils.simple_parse as simple_parse
from execute import Execution
from global_data import GlobalData 
from utils.print import debug_log

## PARSE ARGS 
parser = argparse.ArgumentParser(description="")
parser.add_argument('--split', '-n', type=int, default=2)
parser.add_argument('--input', '-i', type=str)
parser.add_argument('--script', '-s', type=str)
parser.add_argument('--output', '-o', type=str)
parser.add_argument('-id', type=int)
parser.add_argument('--agg_set', '-agg', type=str)
args, cmds = parser.parse_known_args() 

def run_cmd_loop(globals: GlobalData) -> str: 
    cmds = simple_parse.parse_pipeline(args.script)   
    debug_log(f'command instances:  {str(cmds)}; count: {str(len(cmds))}; split: {globals.split}', globals)
    output_path = ""
    for cmd in cmds:
        globals.set_cmd(cmd) 
        debug_log(f'run {cmd} with input {globals.input}', globals)
        curr_execution = Execution(globals)
        output_path = curr_execution.execute_par_or_seq()
        globals.change_input(output_path)
     
    return output_path
    
def run(): 
    globals = GlobalData(args.input, args.script, args.split, args.id, args.agg_set)
    final_output = run_cmd_loop(globals)
    with open(args.output, 'w', newline='\n') as outfile:
        with open(final_output, 'r', encoding='UTF-8-sig', newline='\n') as infile:
            for line in infile:
                outfile.write(line)

run()

        
