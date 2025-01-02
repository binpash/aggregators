#!/usr/bin/env python3

import utils, re, argparse, functools, sys 

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
    
def sed(a: list[str], b: list[str]) -> list[str]: 
    val, action = re.findall(r'\d+|\D+', args.string[0])
    concat = a + b 
    res = None
    if action == "q": 
        res = sed_q(concat, val)
    else: 
        res = concat
    return res

def agg(a, b): 
    return sed(a,b)

try:
    res = functools.reduce(agg, utils.read_all(), [])
    try: 
        utils.out("".join(res)) 
    except: 
        utils.out(b''.join(res))
except Exception as e: 
    print(e.backtrace())
    sys.exit(1)
        
    
    