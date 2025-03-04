#!/usr/bin/env python3

import argparse, functools, utils, re, locale, sys
import operator  

## SORT FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for sort")
parser.add_argument('-n', action='store_true', help="numeric sort")
parser.add_argument('-k', type=int, default=0, help="with key")
parser.add_argument('-r', action='store_true', help="reverse sort; larger values goes in front")
parser.add_argument('-u', action='store_true', help="uniq sort")
parser.add_argument('-f', action='store_true', help="ignore case sort")
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args()

# set correct locale 
locale_str = utils.getExactLocale()
locale.setlocale(locale.LC_COLLATE, f"{locale_str}") # ensure locale is correct 

## SORT UTILS FUNCTIONS ## 
def atof(str):
    try:
        retval = locale.atof(str)
        return retval
    except ValueError:
        retval = str
        return None 

def natural_keys(str):
    nat_key = 0
    str = str.strip()
    for i in range(len(str)):
        if atof(str[:i+1]) != None: 
            nat_key = atof(str[:i+1])
            continue 
        else: 
            break
    return nat_key 
        
        

## COMPARE FUNC ## 
# compare based on numerical values 
def compare_num(a,b): 
    res = [a,b]
    a.strip()
    b.strip()
    try: 
        if args.k > 0: 
            res = sorted(res, key=operator.itemgetter(args.k)) 
        a_nat_key = natural_keys(a)
        b_nat_key = natural_keys(b)
        if a_nat_key > b_nat_key: 
            return 1
        if b_nat_key > a_nat_key: 
            return -1
        res = sorted(res, key=locale.strxfrm) 
    except:
        res = sorted(res, key=locale.strxfrm)
    return -1 if res[0] == a else 1 
 
# compare based on number and alphabetical chars only 
def compare_alphanum(a,b): 
    res = [a, b] 
    res = sorted(res, key=locale.strxfrm) # cmp using correct locale
    if args.f:
        res = sorted(res, key=functools.cmp_to_key(locale.strcoll))
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
    #     1. cmp a and b using default sort 
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
                res.append(a_list[a_curr]) # a is smaller (goes in front)
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

def sort_basic_n(a_list, b_list):
    res = []
    # while both idx are in bound, 
    #     1. cmp a and b using default sort 
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
                res.append(a_list[a_curr]) # a is smaller (goes in front)
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

try: 
    res = functools.reduce(agg, utils.read_all(), [])
    try: 
        utils.out("".join(res)) 
    except: 
        for line in res: 
            utils.out(line)
except Exception as e: 
    print(e.traceback())
    sys.exit(1) # execute sequentially
    
# if __name__ == '__main__':
#     res = functools.reduce(agg, utils.read_all(), [])
#     print(res)