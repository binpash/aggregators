#!/usr/bin/env python3

import utils, re, argparse, functools, sys 

## WC FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for wc")
parser.add_argument('-l', action='store_true', help="line count")
parser.add_argument('-c', action='store_true', help="byte count")
parser.add_argument('-w', action='store_true', help="word count")
parser.add_argument('-m', action='store_true', help="char count")
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args()

def wc(parallel_res: list[str]):
    # maintain string pad length by splitting when number ends
    r = "\s*\d+" # for measuring padding size
    build_sum = parallel_res[0]
    for res in parallel_res[1:]:
        if res == None or res.strip() == "": continue 
        build_sum = "".join(str(int(x) + int(y)).rjust(len(x)) for x, y in zip(re.findall(r, build_sum), re.findall(r, res)))
    return build_sum  

    
def agg(a, b):
    if len(a) == 0: 
        parallel_res = [str(b)]
    elif len(b) == 0: 
        parallel_res = [str(a)]
    else: 
        parallel_res = [str(a),str(b)]
    return wc(parallel_res)

try: 
    res = functools.reduce(agg, utils.read_all(), [])
    utils.out("".join(res)) 
except: 
    sys.exit(1) # execute sequentially