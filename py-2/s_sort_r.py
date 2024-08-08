#!/usr/bin/python3

import functools, utils, locale

# compare based on number and alphabetical chars only 
def compare_alphanum(a,b): 
    res = [a,b]
    my_locale = locale.getlocale()
    locale.setlocale(locale.LC_ALL, my_locale) # ensure locale is correct 
    res = sorted(res, key=locale.strxfrm, reverse=False) # cmp using correct locale
    return -1 if res[0] == a else 1 

def sort_basic(a_list, b_list):
    res = []
    # while both idx are in bound, 
    #     1. comp a and b, 
    #     2. add smaller to res,  
    #     3. incr a | b ptr (smaller) 
    
    a_curr, b_curr = 0, 0 
    while a_curr < len(a_list) and b_curr < len(b_list):  
        comp_res = compare_alphanum(a_list[a_curr], b_list[b_curr])
        if (comp_res > 0):
            # a is smaller (goes in front)
            res.append(a_list[a_curr]) 
            a_curr += 1 
        else: 
            res.append(b_list[b_curr])
            b_curr += 1 
    
    # if h1 ended, add all h2; else add all h1
    if a_curr < len(a_list): 
        res = res + a_list[a_curr:]
    if b_curr < len(b_list): 
        res = res + b_list[b_curr:]
    return res

def agg(a, b):
    return sort_basic(a,b)

res = functools.reduce(agg, utils.read_all(), [])
utils.out("".join(res))
