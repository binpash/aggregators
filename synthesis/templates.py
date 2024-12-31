# templates.py

GENERAL_TEMPLATE = """
import Synthesis

{extra_imports}

{helper_functions}

def main (args : List String) : IO UInt32 := do
  {stream_initialization}
  {processing_logic}
  {output_logic}
  return 0
"""


CMP_TEMPLATE = """
def cmp (a b : {input_type}) : Bool :=
  {comparison_logic}
"""

PARSE_TEMPLATE = """
def parseInput (lines : List String) : {input_type} :=
  {parsing_logic}
"""

MERGE_LOGIC = """ 
def mergeLogic (acc : {accumulator_type}) (input : {input_type}) : {accumulator_type} :=
  {merge_logic}
"""
