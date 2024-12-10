from os import write
import infra_run as globals

def debug_log(log: str): 
    prefix = f'{globals.cmd}: '  
    with open(globals.debug_log_path, 'w') as debug_log:
        write(debug_log, f'{prefix}{log}') 
        
        
