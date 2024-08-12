#!/usr/bin/env python3

import argparse, functools, utils, re, locale

## SORT FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for sort")
parser.add_argument('-n', action='store_true', help="numeric sort")
parser.add_argument('-r', action='store_true', help="reverse sort; larger values goes in front")
parser.add_argument('-u', action='store_true', help="uniq sort")
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args()

locale.setlocale(locale.LC_ALL, "") # ensure locale is correct 

## SORT UTILS FUNCTIONS ## 
def atof(str):
    try:
        retval = float(str)
        return retval
    except ValueError:
        retval = str
        return str

def natural_keys(str):
    parts = re.split(r'([0-9]*\.?[0-9]*)', str.strip())
    return [atof(c) for c in parts if c]

## COMPARE FUNC ## 
# compare based on numerical values 
def compare_num(a,b): 
    res = [a,b]
    a.strip()
    b.strip()
    try: 
        res = sorted(res, key=natural_keys) # cmp using correct locale, by float 
        if res[0].split()[0] == res[1].split()[0]: 
            res = sorted(res, key=locale.strxfrm) # ensure rest of string is sorted normally if num is same
    except:
        res = sorted(res, key=locale.strxfrm) 
    return -1 if res[0] == a else 1 
 
# compare based on number and alphabetical chars only 
def compare_alphanum(a,b): 
    res = [a,b] 
    res = sorted(res, key=locale.strxfrm) # cmp using correct locale
    return -1 if res[0] == a else 1

# determine which compare function to use
def compare(a,b): 
    if args.n: 
        return compare_num(a,b)
    else: 
        return compare_alphanum(a,b)
    
## MAIN SORT ## 
def sort_basic(a_list, b_list):
    res = []
    # while both idx are in bound, 
    #     1. comp a and b, 
    #     2. add smaller to res,  
    #     3. incr a | b ptr (smaller) 
    
    a_curr, b_curr = 0, 0 
    while a_curr < len(a_list) and b_curr < len(b_list):
        if args.u and a_list[a_curr] == b_list[b_curr]:
            b_curr += 1 # skip over b to not consider the same value
        else:  
            comp_res = compare(a_list[a_curr], b_list[b_curr])
            if args.r:
                comp_res *= -1    
            if (comp_res < 0):
                # a is smaller (goes in front)
                res.append(a_list[a_curr]) 
                a_curr += 1 
            else: 
                res.append(b_list[b_curr])
                b_curr += 1 
        
    # if a ended, add all b; else add all a
    if a_curr < len(a_list): 
        res = res + a_list[a_curr:]
    if b_curr < len(b_list): 
        res = res + b_list[b_curr:]
    return res

def agg(a, b):
    return sort_basic(a,b)

res = functools.reduce(agg, utils.read_all(), [])
utils.out("".join(res)) 