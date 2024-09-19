#!/bin/bash
# Calculate mispelled words in an input
# https://dl.acm.org/doi/10.1145/3532.315102

# dict=$SUITE_DIR/inputs/dict.txt

# cat $1 |
#     iconv -f utf-8 -t ascii//translit | # remove non utf8 characters
#     # groff -t -e -mandoc -Tascii |  # remove formatting commands
#     col -bx |                      # remove backspaces / linefeeds
#     tr -cs A-Za-z '\n' |
#     tr A-Z a-z |                   # map upper to lower case
#     tr -d '[:punct:]' |            # remove punctuation
#     sort |                         # put words in alphabetical order
#     uniq |                         # remove duplicate words
#     comm -23 - $dict               # report words not in dictionary 

# modified original script above to take out main pipeline relevant to agg. 
cat $1 | iconv -f utf-8 -t ascii//translit | col -bx | tr -cs A-Za-z '\n' | tr A-Z a-z | tr -d '[:punct:]' | sort | uniq | comm -23 - inputs/dict.txt     
