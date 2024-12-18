#!/usr/bin/env python3

import argparse, sys
import utils.simple_parse as simple_parse
from execute import Execution
from global_data import GlobalData 
from utils.print import debug_log,metrics_csv_row

parser = argparse.ArgumentParser(description="a naive parallelization of linux cmds separated by pipes")
try: 
    parser.add_argument('--split', '-n', type=int, default=2, help="parallelization degree")
    parser.add_argument('--input', '-i', type=str, help="input to script")
    parser.add_argument('--script', '-s', type=str, help="bash script for parallelized execution; script should be in form of `$cat | <cmd> | <cmd> ..` ")
    parser.add_argument('--output', '-o', type=str, help="target output after parallelization")
    parser.add_argument('--input-inflation', '-inflate', help="include flag to inflates all input to roughly the same size between each command instance", action='store_true')
    parser.add_argument('--input-random', '-random', type=int, default=0, help="/dev/random of [byte size] for all input to each stage")
    parser.add_argument('--id', '-id', type=int, help="unique id to this run")
    parser.add_argument('--agg-set', '-agg', type=str, help="list path to aggregators or quick access to predefined set of aggregators using [lean], [python], or [all]")
    args, cmds = parser.parse_known_args() 
except: 
    parser.print_help()
    sys.exit(2)

def run_cmd_loop(globals: GlobalData) -> str: 
    cmds = simple_parse.parse_pipeline(args.script)   
    debug_log(f'command instances:  {str(cmds)}; count: {str(len(cmds))}; split: {globals.split}; script: {globals.script}; id: {globals.id}', globals)
    output_path = ""
    for idx, cmd in enumerate(cmds):
        debug_log("\n", globals)
        globals.set_cmd(cmd) 
        debug_log(f'CMD INSTANCE {idx + 1}: {cmd}', globals)
        debug_log(f'Input: {globals.input}; Org input size: {globals.org_input_size}; Inf input size: {globals.inf_input_size}', globals)
        curr_execution = Execution(globals)
        output_path = curr_execution.execute_par_or_seq()
        metrics_csv_row(f'{globals.metadata_to_header()}{globals.d}{curr_execution.metric_row}', globals)
        globals.change_input(output_path)
    return output_path
    
def run():
    try:  
        globals = GlobalData(args.input, args.script, args.split, args.id, args.agg_set, args.input_inflation, args.input_random)
    except Exception as e:
        print(e, e.backtrace()) 
        parser.print_help()
        sys.exit(2)
    final_output = run_cmd_loop(globals)
    with open(args.output, 'w', newline='\n') as outfile:
        with open(final_output, 'r', newline='\n') as infile:
            for line in infile:
                outfile.write(line)
    debug_log(f"DONE\n \n", globals)

run()

        
