from os import path, makedirs

# All None attributes should be set at runtime. 
# All other attributes should be pre-set before runtime. 

class GlobalData: 
    def __init__(self, input_: str, script_: str, split_: str, 
                    id_: int, agg_set_: str):
        self.input = input_ 
        self.input_name = path.splitext(path.basename(self.input))[0] 
        self.script = script_
        self.script_name = path.splitext(path.basename(self.script))[0]
        self.split= split_
        self.id= id_
        self.agg_set=agg_set_ 

        self.simple_infra_path = "../simple_infra/"
        self.inter_dir_path = f'inputs-s-{str(self.id)}/' 
        self.output_dir_path = "outputs-temp/agg/"
        self.check_par_output_dir_path = "outputs-temp/seq-check/"
        self.par_path =  self.simple_infra_path + "exec_scripts/test-par-driver.sh"
        self.seq_path = self.simple_infra_path + "exec_scripts/test-seq-driver.sh"
        self.debug_log_path = "infra_debug.log"
        
        self.cmd = None
        self.split_file_dir = None 
        
        self.setup_dir()
        
    def change_input(self, new_input: str): 
        self.input = new_input  
        self.input_name = path.splitext(path.basename(self.input))[0]

    def set_script(self, new_script: str): 
        self.script = new_script 
        self.script_name = path.splitext(path.basename(self.script))[0]
        
    def set_cmd(self, new_cmd: str): 
        self.cmd = new_cmd
        self.split_file_dir = f'{self.inter_dir_path}{self.input_name}/'
        

    def setup_dir(self): 
        if not path.exists(self.output_dir_path): 
            makedirs(self.output_dir_path)
            
        if not path.exists(self.check_par_output_dir_path): 
            makedirs(self.check_par_output_dir_path)

        if not path.exists(self.inter_dir_path):
            makedirs(self.inter_dir_path)
    

