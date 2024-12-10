from global_data import GlobalData
from os import listdir
from os.path import isfile, join 

class Execution: 
    def __init__(self, globals_: GlobalData): 
        self.g = globals_

    def get_executed_output_and_time(self, byte_str: str): 
        parse_output = byte_str.decode('utf-8').split(",")
        executed = parse_output[0]
        output = parse_output[1]
        time = parse_output[2].strip()
        return (executed, output, time)
    
    def generate_seq_expected(self): 
        seq_out = f'{self.g.check_par_output_dir_path}{self.g.input_name}-{self.g.cmd}.txt'
        if not os.path.exists(seq_out): 
            seq_execute = subprocess.check_output([self.g.seq_path, self.g.input, 
                                                self.g.check_par_output_dir_path, 
                                                self.g.cmd])
            seq_e, seq_out, seq_time = self.get_executed_output_and_time(seq_execute)  
            debug_log_exec(seq_e, seq_out, seq_time, self.g)
        return seq_out 
        

    def check_aggregator_correctness(self, par_result: str, seq_expectd: str) -> bool: 
        rv = subprocess.run(['diff', '-q', par_result, seq_expectd], capture_output=True).returncode
        return rv == 0
        

    def generate_partials(self):
        # Split files and set-up intermediate directory paths. 
        split_file_dir_org = f"{self.g.split_file_dir}org/"
        split_file_dir_cmd = f"{self.g.split_file_dir}cmd/"
        if not os.path.exists(split_file_dir_org): 
            os.makedirs(split_file_dir_org)
        else: 
            split_file = [split_file_dir_org + f for f in listdir(split_file_dir_org) if isfile(join(split_file_dir_org, f))]
        if not os.path.exists(split_file_dir_cmd): 
            os.makedirs(split_file_dir_cmd)
        else: 
            return (split_file, split_file_dir_cmd)
        split_files = simple_split.split_file(self.g.input, self.g.split, f"{split_file_dir_org}")
        
        # Apply cmd to each partials. 
        partials_after_cmd = []
        for file in split_files: 
            seq_execute_partial = subprocess.check_output([self.g.seq_path, file, 
                                                           split_file_dir_cmd, 
                                                           self.g.cmd]) 
            partials_after_cmd.append(self.get_executed_output_and_time(seq_execute_partial)[1])
        return (split_files, split_file_dir_cmd)

    def combine_partials_with_aggregator(self, agg:str, agg_set: str, split_file_dir_cmd: str, split_files: str): 
        output_dir_path_with_idx = self.g.output_dir_path + agg_set + "/"
        if not os.path.exists(output_dir_path_with_idx): 
            os.makedirs(output_dir_path_with_idx)
        par_execute = subprocess.check_output([self.g.par_path, self.g.input, 
                                               output_dir_path_with_idx, 
                                               self.g.cmd, agg, split_file_dir_cmd])
        # debug_log(f'execute {self.g.cmd}: applied {agg} to combine {len(split_files)} partials, {split_files}', self.g)
        par_e, par_out, par_time = self.get_executed_output_and_time(par_execute)
        debug_log_exec(par_e, par_out, par_time, self.g)
        return par_out 
        
        
    def execute_par(self, agg_set: int, agg: str) -> str: 
        # Split files, set-up intermediate directory paths, and apply cmd to each partials.
        split_files, split_file_dir_cmd = self.generate_partials()
        
        # Apply aggregator to combine partials. 
        par_out = self.combine_partials_with_aggregator(agg, agg_set, split_file_dir_cmd, split_files)
        
        # Check if aggregator is correct against seq expected. 
        seq_out = self.generate_seq_expected()
        if (self.check_aggregator_correctness(par_out, seq_out)): 
            debug_log(f'execute {self.g.cmd}: {agg} correct, return par: {par_out}', self.g)
            return par_out
        else: 
            debug_log(f'execute {self.g.cmd}: {agg} incorrect, return seq: {seq_out}', self.g)
            return seq_out
        
    def execute_seq(self) -> str: 
        seq_execute = subprocess.check_output([self.g.seq_path, self.g.input, 
                                               self.g.output_dir_path, 
                                               self.g.cmd]) 
        e, out, time = self.get_executed_output_and_time(seq_execute)
        debug_log_exec(e, out, time, self.g)
        return out 

    def execute_par_or_seq(self) -> str: 
        has_valid_agg = self.g.check_aggregator_exists() 
    
        # If aggregator found, use parallel execution. 
        # If parallel execution fails, run sequential instead to not affect next cmd. 
        output_path = ""
        for idx, agg in enumerate(has_valid_agg): 
            if has_valid_agg != "": 
                curr_output_path = self.execute_par(self.g.agg_set[idx], agg)
                output_path = curr_output_path
        
        if output_path is not None: return output_path
            
        # If no aggregator found, use sequential execution. 
        output_path = self.execute_seq()
        return output_path

import os, subprocess
import utils.simple_split as simple_split 
from utils.print import debug_log, debug_log_exec

