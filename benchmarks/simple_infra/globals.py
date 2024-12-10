from os import path, makedirs

# All None attributes should be set at runtime. 
# All other attributes should be pre-set before runtime.  
cmd = None
input = None
input_name = None
script = None
split= None
script_name = None
id=None
agg_set=None

simple_infra_path = "../simple_infra/"
inter_dir_path = None
split_file_dir = None
output_dir_path = "outputs-temp/agg/"
check_par_output_dir_path = "outputs-temp/seq-check/"
par_path =  simple_infra_path + "exec_scripts/test-par-driver.sh"
seq_path = simple_infra_path + "exec_scripts/test-seq-driver.sh"
debug_log_path = "infra_debug.log"


def change_input(new_input: str): 
    global input 
    input = new_input  
    
    global input_name
    input_name = path.splitext(path.basename(input))[0]

def set_script(new_script: str): 
    global script 
    script = new_script  
    
    global script_name
    script_name = path.splitext(path.basename(script))[0]
    
def set_cmd(new_cmd: str): 
    global cmd 
    cmd = new_cmd
    
    global split_file_dir
    split_file_dir = f'{inter_dir_path}{input_name}/'
    

def setup_dir(): 
    if not path.exists(output_dir_path): 
        makedirs(output_dir_path)
        
    if not path.exists(check_par_output_dir_path): 
        makedirs(check_par_output_dir_path)

    if not path.exists(inter_dir_path):
        makedirs(inter_dir_path)

def setup_global_files(input_, script_, split_, id_, agg_set_): 
    change_input(input_)
    set_script(script_)
    global split 
    split = split_
    
    global id 
    id = id_
    
    global inter_dir_path
    inter_dir_path = f'inputs-s-{str(id)}/' 
    
    global agg_set 
    agg_set = agg_set_