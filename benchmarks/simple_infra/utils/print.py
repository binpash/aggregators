from global_data import GlobalData

def debug_log(log: str, globals: GlobalData): 
    prefix = f'{globals.script_name}: '  
    with open(globals.debug_log_path, 'a') as debug_log:
        debug_log.write(f'{prefix}{log}\n') 

def debug_log_exec(e: str, o:str, t:str, globals: GlobalData): 
    prefix = f'{globals.script_name}: '  
    with open(globals.debug_log_path, 'a') as debug_log:
        debug_log.write(f'{prefix}{e}, {t}\n')         
        
# def metrics_csv_row(globals:GlobalData): 
#     with open(globals.metrics_path, 'a') as m_log:
#         m_log.write(f'{}, {t}\n')     
        
def metrics_csv_header(globals: GlobalData): 
    meta_header = "script,input,input size,adj input size,cmd"
    py_header = "py agg,py agg time,py agg correct,py seq"
    lean_header = "lean agg,lean agg time,lean agg correct,lean seq"
    header = ""
    for agg in globals.agg_set: 
        if agg == "all": 
            header += f'{meta_header},{py_header},{lean_header}'  
        elif agg == "lean": 
            header += f'{meta_header},{lean_header}'    
        else: 
           header += f'{meta_header},{py_header}'    
    with open(globals.metrics_path, 'a') as m_log:
        m_log.write(header + "\n")
    