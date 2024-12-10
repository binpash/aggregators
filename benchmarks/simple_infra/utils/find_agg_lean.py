#!/usr/bin/env python3

from os import path 

def find_lean(cmd: str, flag: str, args): 
    if cmd == "grep": 
        return "concat"
    elif cmd == "wc": 
        return "sum"
    elif cmd == "sort" and "r" in flag and "n" in flag: 
        return "sortnr"
    elif cmd == "sort" and "u" in flag: 
        return ""
    elif cmd == "sort" and "r" in flag: 
        return "sortr"
    elif cmd == "sort" and "n" in flag: 
        return "sortn"
    elif cmd == "sort": 
        return "sort"
    elif cmd == "uniq" and "c" in flag: 
        return "uniqc"
    elif cmd == "uniq": 
        return "uniq" 
    elif cmd == "head" and "n" in flag and args[0] == '1': 
        return "headn1" 
    elif cmd == "head": 
        return ""
    elif cmd == "tail" and "n" in flag and args[0] == '1': 
        return "tailn1"
    elif cmd == "tail": 
        return ""
    elif cmd == "xargs": 
        return ""
    else: 
        return "concat"
    
def find(cmd: str, agg_dir_path: str):
    cmd_in_list = cmd.split() 
    if len(cmd_in_list) == 1: 
        binary_name = find_lean(cmd_in_list[0], "", []) 
    elif len(cmd_in_list) == 2: 
        binary_name = find_lean(cmd_in_list[0], cmd_in_list[1], []) 
    else: 
        binary_name = find_lean(cmd_in_list[0], cmd_in_list[1], cmd_in_list[2:])
   
    agg_file = agg_dir_path + binary_name
    if path.isfile(agg_file): 
        return agg_file
    else: 
        return ""
    

 