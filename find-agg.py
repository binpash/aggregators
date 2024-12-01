#!/usr/bin/env python3

import argparse 

## PARSE ARGS ##
parser = argparse.ArgumentParser(description="Check which commands and flags we are using to find lean binary")

## FLAGS
parser.add_argument('-c', action='store_true')
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
parser.add_argument('-w', action='store_true')
parser.add_argument('-m', action='store_true')
# args, unknown = parser.parse_known_args()
args, cmds = parser.parse_known_args()

def match_agg(): 
    cmd = ""
    if cmds: 
        cmd = cmds[0]
    
    if cmd == "grep": 
        return "concat"
    elif cmd == "wc": 
        return "sum"
    elif cmd == "sort" and args.n and args.r: 
        return "sortnr"
    elif cmd == "sort" and args.nr: 
        return "sortnr"
    elif cmd == "sort" and args.u: 
        return ""
    elif cmd == "sort" and args.rn: 
        return "sortnr"
    elif cmd == "sort" and args.r: 
        return "sortr"
    elif cmd == "sort" and args.n: 
        return "sortn"
    elif cmd == "sort": 
        return "sort"
    elif cmd == "uniq" and args.c: 
        return "uniqc"
    elif cmd == "uniq": 
        return "uniq" 
    elif cmd == "head" and args.n: 
        return "headn1" 
    elif cmd == "tail" and args.n: 
        return "tailn1"
    else: 
        return "concat"

print(match_agg())

 


