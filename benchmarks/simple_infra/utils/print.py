from global_data import GlobalData


def debug_log(log: str, globals: GlobalData): 
    prefix = globals.debug_prefix
    with open(globals.debug_log_path, 'a') as debug_log:
        debug_log.write(f'{prefix}{log}\n') 

def debug_log_exec(e: str, o:str, t:str, globals: GlobalData): 
    prefix = globals.debug_prefix
    with open(globals.debug_log_path, 'a') as debug_log:
        debug_log.write(f'{prefix}script ran: {e}, {t}\n')         
        
def metrics_csv_row(row: str, globals:GlobalData): 
    with open(globals.metrics_path, 'a') as m_log:
        m_log.write(f'{row}\n')     
        
def metrics_csv_header(globals: GlobalData): 
    meta_header = "script,input,input size,adj input size,cmd"
    py_header = "py agg,py agg time,py agg correct,py seq"
    lean_header = "lean agg,lean agg time,lean agg correct,lean seq"
    header = meta_header
    for agg in globals.agg_set: 
        if agg == "lean": 
            header += f',{lean_header}'    
        else: 
           header += f',{py_header}'    
    with open(globals.metrics_path, 'a') as m_log:
        m_log.write(header + "\n")
    