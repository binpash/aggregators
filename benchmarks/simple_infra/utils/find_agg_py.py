from os import path 

default_concat_agg = "s_grep.py"
no_agg_list = ["tail", "head"]

def find(cmd: str, agg_dir_path: str): 
    cmd_in_list = cmd.split() # sort -rn -> [sort, -rn]
    agg = "s_" + cmd_in_list[0]+ ".py"
    flag = ""
    if len(cmd_in_list) > 1 and cmd_in_list[1][0] == "-": 
        flag = " ".join(cmd_in_list[1:])
    agg_file = agg_dir_path + agg 
    
    # check if agg. actually exist 
    if cmd_in_list[0] in no_agg_list: 
        return "" 
    elif path.isfile(agg_file):
        return f'{agg_file} {flag}'
    else: 
        agg_file = agg_dir_path + default_concat_agg
        if path.isfile(agg_file): 
            return agg_file
        else: 
            return "" 


