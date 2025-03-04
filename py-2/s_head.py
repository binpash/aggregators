#!/usr/bin/env python3

import utils, re, argparse, functools, sys 

## SED FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for head")
parser.add_argument('-n', type=int, default=1)
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args() 

def head(a: list[str], b: list[str]) -> list[str]: 
    concat = a + b
    if args.n <= len(concat): 
        return concat[:args.n]
    else: 
        return concat
    
def agg(a, b): 
    args.n = abs(args.n)
    return head(a,b)

try: 
    res = functools.reduce(agg, utils.read_all(), [])
    utils.out("".join(res)) 
except: 
    sys.exit(1) # execute sequentially
    
    
    