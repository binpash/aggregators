#!/usr/bin/env python3

import utils, re, argparse, itertools, sys

## SED FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for head")
parser.add_argument('-n', type=str)
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args() 

def tail(concat: list[str], action: str, val: int) -> list[str]: 
    if action == "+" and val <= len(concat): 
            return concat[val - 1:]
    
    if action == "" and val <= len(concat): 
            return concat[-val:]
        
    return concat


def agg(res: list[str]): 
    try: 
        action, val = re.findall(r'\d+|\D+', args.n)
    except: 
        action = ""
        val = args.n
    
    val = abs(int(val))
    return tail(res, action, val)
    
try: 
    concat_file_read = utils.read_all()
    res = agg(list(itertools.chain(*concat_file_read)))
    utils.out("".join(res)) 
except: 
    sys.exit(1) # execute sequentially
