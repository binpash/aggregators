#!/usr/bin/env python3
import functools, utils

# TODO: add in flags 
#   head currently do not support flags (i.e. -n) as 
#   result may be taken from final parallel segment only 

def agg(a, b):
  if not a:
    return b
  return b

res = functools.reduce(agg, utils.read_all(), [])
utils.out("".join(res))

