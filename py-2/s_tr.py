#!/usr/bin/env python3

import utils, argparse, itertools, sys, subprocess

## GREP FLAGS ##
parser = argparse.ArgumentParser(description="Check which flags we use for grep")
parser.add_argument('-c', action='store_true')
parser.add_argument('-s', action='store_true')
parser.add_argument('-d', action='store_true')
parser.add_argument('string', nargs=2, help="input files to sort agg")
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args()

# grep -c
def tr_sc(concat: list[str]) -> list[str]:
    file_obj = args.file 
    files = " ".join([file.name for file in file_obj])
    tr_args = " ".join([f"'{arg}'" for arg in args.string])
    output = subprocess.run(f"cat {files} | tr -sc {tr_args}", shell=True, capture_output=True, text=True).stdout
    return output
    
def agg(res: list[str]) -> list[str]: 
    if args.c and args.s:
        return tr_sc(res)
    else: 
        return res

try:
    concat_file_read = utils.read_all()
    res = agg(list(itertools.chain(*concat_file_read)))
    try: 
        utils.out("".join(res)) 
    except: 
        utils.out(b''.join(res))
except Exception as e: 
    print(e.traceback())
    sys.exit(1)
    

# res = functools.reduce(agg, utils.read_all(), [])
# utils.out("".join(res)) 