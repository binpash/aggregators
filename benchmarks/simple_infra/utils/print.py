from global_data import GlobalData

def debug_log(log: str, globals: GlobalData): 
    prefix = f'{globals.script_name}: '  
    with open(globals.debug_log_path, 'a') as debug_log:
        debug_log.write(f'{prefix}{log}\n') 

def debug_log_e(e: str, o:str, t:str, globals: GlobalData): 
    prefix = f'{globals.script_name}: '  
    with open(globals.debug_log_path, 'a') as debug_log:
        debug_log.write(f'{prefix}{e}, {t}\n')         
        