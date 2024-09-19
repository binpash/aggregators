#!/usr/bin/env python3
import functools, argparse, utils, sys

## SORT FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for uniq")
parser.add_argument('-c', action='store_true', help="count uniq")
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args()

## UTILS FOR UNIQ ## 
def combinePair(a, b):
  if (a == b):
    return [a]
  else:
    return [a, b] # already strings, no need to emit


## UTILS FOR uniq -c ## 
def findPadLen(s): 
  return len(s) - len(s.lstrip())

def parseLine(s):
  res = s.split(None, 1)
  try: 
    return (int(res[0]), res[1])
  except: 
    res.append(" ") # empty line (i.e. ' 1   ' )
    return (int(res[0]), res[1])

def emitLine(t, PAD_LEN): 
  return " " * PAD_LEN + str(t[0]) + " " + t[1]  # pad with " " x PAD_LEN 

def combinePair_c(a, b):
  az = parseLine(a)
  bz = parseLine(b) 
  if (az[1:] == bz[1:]):
    # set PAD_LEN to be min, in case we have " 23 f" + "  1 f", we take PAD_LEN for str1
    pad_len = min(findPadLen(a), findPadLen(b))
    adj = len(str(az[0] + bz[0])) - max(len(str(az[0])), len(str(bz[0])))
    pad_len -= adj
    return [emitLine([az[0] + bz[0], az[1]], pad_len)]
  else:
    return [a, b] # already strings, no need to emit

def agg(a, b):
  if args.c: 
    if not a:
      return b
    pair = combinePair_c(a[-1], b[0])
    return a[:-1]  + pair + b[1:]
  else: 
    if not a:
      return b
    pair = combinePair(a[-1], b[0]) # take last + first, combine if equal and add
    return a[:-1]  + pair + b[1:]

try: 
  res = functools.reduce(agg, utils.read_all(), [])
  utils.out("".join(res))
except UnicodeDecodeError: 
  sys.exit(1) # execute sequentially
