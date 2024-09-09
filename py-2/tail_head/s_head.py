#!/usr/bin/env python3
import functools, utils

def agg(a, b):
  if not a:
    return b
  return a

res = functools.reduce(agg, utils.read_all(), [])
utils.out("".join(res))
