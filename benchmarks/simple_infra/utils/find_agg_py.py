from os import path, chmod, stat
from stat import S_IEXEC

default_concat_agg = "s_grep.py"
no_agg_list = []

def find(cmd: str, agg_dir_path: str): 
    cmd_in_list = cmd.split() # sort -rn -> [sort, -rn]
    agg = "s_" + cmd_in_list[0]+ ".py"
    flag = ""
    if len(cmd_in_list) > 1 and cmd_in_list[1][0] == "-": 
        flag = " ".join(cmd_in_list[1:])
    if cmd_in_list[0] == "sed": 
        flag = " ".join(cmd_in_list[1:])
    agg_file = agg_dir_path + agg 
    
    # check if agg. actually exist 
    if cmd_in_list[0] in no_agg_list: 
        return "" 
    elif path.isfile(agg_file):
        st = stat(agg_file)
        chmod(agg_file, st.st_mode | S_IEXEC)
        return f'{agg_file} {flag}'
    else: 
        agg_file = agg_dir_path + default_concat_agg
        st = stat(agg_file)
        chmod(agg_file, st.st_mode | S_IEXEC)
        if path.isfile(agg_file): 
            return agg_file
        else: 
            return "" 


