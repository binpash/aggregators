#!/usr/bin/env python3

import utils, argparse, functools, sys

## GREP FLAGS ##
parser = argparse.ArgumentParser(description="Check which flags we use for grep")
parser.add_argument('-c', action='store_true')
parser.add_argument('-cs', action='store_true')
parser.add_argument('-i', action='store_true')
parser.add_argument('-e', action='store_true')
parser.add_argument('-v', action='store_true')
parser.add_argument('-n', action='store_true')
parser.add_argument('-k', action='store_true')
parser.add_argument('-r', action='store_true')
parser.add_argument('-rn', action='store_true')
parser.add_argument('-nr', action='store_true')
parser.add_argument('-u', action='store_true')
parser.add_argument('-f', action='store_true')
parser.add_argument('-l', action='store_true')
parser.add_argument('-L', action='store_true')
parser.add_argument('-w', action='store_true')
parser.add_argument('-m', action='store_true')
parser.add_argument('-d:', action='store_true')
parser.add_argument('-f1', action='store_true')
args, unknown = parser.parse_known_args()

# for most grep [-flag]
def grep(a, b): 
    return a + b

# grep -c
def grep_c(a,b):
    if len(a) == 0: 
        return b
    elif len(b) == 0: 
        return a
    else: 
        parallel_res = [str(a),str(b)]
        num1 = int(parallel_res[0].strip("[]'\\n"))  
        num2 = int(parallel_res[1].strip("[]'\\n"))  
        return str(num1 + num2)
    
def agg(a, b): 
    if args.c:
        return grep_c(a,b)
    else: 
        return grep(a, b)

try: 
    res = functools.reduce(agg, utils.read_all(), [])
    utils.out("".join(res)) 
except: 
    sys.exit(1) # execute sequentially