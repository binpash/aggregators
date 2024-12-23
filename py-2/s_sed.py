#!/usr/bin/env python3

import utils, re, argparse, itertools, sys 

## SED FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for sed")
parser.add_argument('string', nargs=1, help="input files to sort agg")
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args() 

def sed_q(concat: list[str], val: int) -> list[str]: 
    val = int(val)
    if val <= len(concat): 
        return concat[:val]
    else: 
        return concat

def sed_d(concat: list[str], val: int) -> str: 
    val = int(val)
    if val > len(concat): 
        return concat
    elif val == -1: 
        return concat[:-1]
    else:  
        concat.pop(val - 1)
        return concat

def sed(concat: list[str]) -> list[str]: 
    try: 
        val, action = re.findall(r'\d+|\D+', args.string[0])
    except: 
        if "$d" in args.string[0]: 
            val = -1 
            action = "d"
        else: 
            action = None
    res = None
    # print(action, " action", val, " val")
    if action == "q": 
        res = sed_q(concat, val)
    elif action == "d": 
        res = sed_d(concat, val)
    else: 
        return concat
    return res
     
def agg(res: list[str]): 
    return sed(res)

try:
    concat_file_read = utils.read_all()
    res = agg(list(itertools.chain(*concat_file_read)))
    utils.out("".join(res)) 
except: 
    sys.exit(1)
        
    
    