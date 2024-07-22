#!/usr/bin/env python3
import functools, utils, sys 

PAD_LEN = None  

def parseLine(s):
  global PAD_LEN
  if PAD_LEN == None : PAD_LEN = 7
  res = s.split(None, 1)
  try: 
    return (int(res[0]), res[1])
  except: 
    # empty line (i.e. ' 1   ' )
    res.append(" ")
    return (int(res[0]), res[1])

def emitLine(t):
  return " ".join([str(t[0]).rjust(PAD_LEN, ' '), t[1]])

def combinePair(a, b):
  # print(a, b)
  az = parseLine(a)
  bz = parseLine(b)
  if (az[1] == bz[1]):
    return [emitLine([az[0] + bz[0], az[1]])]
  else:
    return [a, b] # already strings, no need to emit

def agg(a, b):
  # print(a, b)
  if not a:
    return b
  return a[:-1]  + combinePair(a[-1], b[0]) + b[1:]

res = functools.reduce(agg, utils.read_all(), [])
utils.out("".join(res))
