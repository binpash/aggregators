#!/usr/bin/env python3

import utils, re, argparse, functools, sys 

## SED FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for sed")
args, unknown = parser.parse_known_args() 

def sed(a, b): 
    val_and_action = re.findall(r'\d+|\D+', unknown)
    print(val_and_action)
    concat = a + b 
    
def agg(a, b): 
    return sed(a,b)

res = functools.reduce(agg, utils.read_all(), [])
utils.out("".join(res)) 
    
if __name__ == '__main__':
    print(res) 
    
    