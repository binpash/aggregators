from global_data import GlobalData
from utils.print import debug_log, debug_log_e

class Execution: 
    def __init__(self, globals_: GlobalData): 
        self.g = globals_

    def get_executed_output_and_time(self, byte_str: str): 
        parse_output = byte_str.decode('utf-8').split(",")
        executed = parse_output[0]
        output = parse_output[1]
        time = parse_output[2].strip()
        return (executed, output, time)

    def check_use_parallel(self):
        if self.g.agg_set == "python": 
            return find_agg_py.find(self.g.cmd, "../../py-2" + "/")
        else:  
            return find_agg_lean.find(self.g.cmd, "../../lean4/.lake/build/bin" + "/")
        

    def check_par_exec(self, par_result: str, seq_expectd: str) -> bool: 
        rv = subprocess.run(['diff', '-q', par_result, seq_expectd]).returncode
        debug_log(f'checking agg correctness: diff {par_result} {seq_expectd}', self.g)
        if rv >= 0: return True

    def create_partials(self):
        # Split files and set-up intermediate directory paths. 
        split_file_dir_org = f"{self.g.split_file_dir}org/"
        split_file_dir_cmd = f"{self.g.split_file_dir}cmd/"
        if not os.path.exists(split_file_dir_org): 
            os.makedirs(split_file_dir_org)
        if not os.path.exists(split_file_dir_cmd): 
            os.makedirs(split_file_dir_cmd)
        split_files = simple_split.split_file(self.g.input, self.g.split, f"{split_file_dir_org}")
        
        # Apply cmd to each partials. 
        partials_after_cmd = []
        for file in split_files: 
            seq_execute_partial = subprocess.check_output([self.g.seq_path, file, 
                                                           split_file_dir_cmd, 
                                                           self.g.cmd]) 
            partials_after_cmd.append(self.get_executed_output_and_time(seq_execute_partial)[1])
        return (split_files, split_file_dir_cmd)
        
    def execute_par(self, agg: str) -> str: 
        # Split files, set-up intermediate directory paths, and apply cmd to each partials. 
        split_files, split_file_dir_cmd = self.create_partials()
        
        # Apply aggregator to combine partials. 
        par_execute = subprocess.check_output([self.g.par_path, self.g.input, 
                                               self.g.output_dir_path, 
                                               self.g.cmd, agg, split_file_dir_cmd])
        debug_log(f'execute {self.g.cmd}: applied {agg} to combine {len(split_files)} partials, {split_files}', self.g)
        seq_execute = subprocess.check_output([self.g.seq_path, self.g.input, 
                                               self.g.check_par_output_dir_path, 
                                               self.g.cmd])
        par_e, par_out, par_time = self.get_executed_output_and_time(par_execute)
        debug_log_e(par_e, par_out, par_time, self.g)
        seq_e, seq_out, seq_time = self.get_executed_output_and_time(seq_execute)  
        debug_log_e(seq_e, seq_out, seq_time, self.g)
        if (self.check_par_exec(par_out, seq_out)): 
            debug_log(f'execute {self.g.cmd}: {agg} correct, return par: {par_out}', self.g)
            return par_out
        else: 
            debug_log(f'execute {self.g.cmd}: {agg} incorrect, return seq: {seq_out}', self.g)
            return seq_out
        
    def execute_seq(self) -> str: 
        if not os.path.exists(input): 
            FileExistsError(input + " not found")
            return ""
        seq_execute = subprocess.check_output([self.g.seq_path, self.g.input, 
                                               self.g.output_dir_path, 
                                               self.g.cmd]) 
        e, out, time = self.get_executed_output_and_time(seq_execute)
        debug_log_e(e, out, time, self.g)
        return out 

    def execute_par_or_seq(self) -> str: 
        has_valid_agg = self.check_use_parallel() 
    
        # If aggregator found, use parallel execution. 
        # If parallel execution fails, run sequential instead to not affect next cmd. 
        if has_valid_agg != "": 
            output_path = self.execute_par(has_valid_agg)
            if output_path is not None: 
                return output_path
            
        # If no aggregator found, use sequential execution. 
        output_path = self.execute_seq()
        return output_path

import os, subprocess
import utils.find_agg_py as find_agg_py
import utils.find_agg_lean as find_agg_lean
import utils.simple_split as simple_split
import utils.print as log 
