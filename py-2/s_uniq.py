#!/usr/bin/env python3
import functools, argparse, utils, sys

## SORT FLAGS ## 
parser = argparse.ArgumentParser(description="Check which flags we use for uniq")
parser.add_argument('-c', action='store_true', help="count uniq")
parser.add_argument('file', type=argparse.FileType('r'), nargs="*", help="input files to sort agg")
args, unknown = parser.parse_known_args()

## UTILS FOR UNIQ ## 
def combinePair(a, b):
  # print(a, b)
  if (a == b):
    return [a]
  else:
    return [a, b] # already strings, no need to emit

def combineBlackbox(a, b):
  return [utils.execute(utils.cmd(), a + b)]

## UTILS FOR UNIQ -c ## 
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

def combinePair_c(a, b):
  # print(a, b)
  az = parseLine(a)
  bz = parseLine(b)
  if (az[1] == bz[1]):
    return [emitLine([az[0] + bz[0], az[1]])]
  else:
    return [a, b] # already strings, no need to emit

def agg(a, b):
  if args.c: 
    if not a:
      return b
    return a[:-1]  + combinePair_c(a[-1], b[0]) + b[1:]
  else: 
    if not a:
      return b
    pair = combinePair(a[-1], b[0])
    # pair = combineBlackbox(a[-1], b[0])
    # print pair
    return a[:-1]  + pair + b[1:]
try: 
  res = functools.reduce(agg, utils.read_all(), [])
  utils.out("".join(res))
except UnicodeDecodeError: 
  sys.exit(1)
