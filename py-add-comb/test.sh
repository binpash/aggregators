#!/bin/bash

# cd inputs
# wget 'https://atlas.cs.brown.edu/data/gutenberg/0/1/old/1.txt' 


cat inputs/1.txt | grep 'and' > outputs/out-seq.txt
cat inputs/1.1.txt | grep 'and' > outputs/out1.txt
cat inputs/1.2.txt | grep 'and' > outputs/out2.txt
combiners/grep.py outputs/out1.txt outputs/out2.txt > outputs/out-par.txt

# grep_c.py
# grep_meta.py
# grep_n.py
# wc.py
