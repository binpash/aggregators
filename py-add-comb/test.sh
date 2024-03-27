#!/bin/bash

# cd inputs
# wget 'https://atlas.cs.brown.edu/data/gutenberg/0/1/old/1.txt' 

CMD="grep Project"
cat inputs/yellow-full.txt | $CMD > outputs/grep-yw-seq.txt
cat inputs/yw-1.txt | $CMD > outputs/grep-yw-1.txt
cat inputs/yw-2.txt | $CMD > outputs/grep-yw-2.txt
python -c 'import grep; grep.combine("outputs/grep-yw-1.txt", "outputs/grep-yw-2.txt")' > outputs/grep-yw-par.txt

CMD="wc"
cat inputs/yellow-full.txt | $CMD > outputs/wc-yw-seq.txt
cat inputs/yw-1.txt | $CMD > outputs/wc-yw-1.txt
cat inputs/yw-2.txt | $CMD > outputs/wc-yw-2.txt
python -c 'import wc; wc.combine("outputs/wc-yw-1.txt", "outputs/wc-yw-2.txt")' > outputs/wc-yw-par.txt

CMD="wc -l"
cat inputs/yellow-full.txt | $CMD > outputs/wc-l-yw-seq.txt
cat inputs/yw-1.txt | $CMD > outputs/wc-l-yw-1.txt
cat inputs/yw-2.txt | $CMD > outputs/wc-l-yw-2.txt
python -c 'import wc; wc.combine("outputs/wc-l-yw-1.txt", "outputs/wc-l-yw-2.txt")' > outputs/wc-l-yw-par.txt

CMD="wc -lm"
cat inputs/yellow-full.txt | $CMD > outputs/wc-lm-yw-seq.txt
cat inputs/yw-1.txt | $CMD > outputs/wc-lm-yw-1.txt
cat inputs/yw-2.txt | $CMD > outputs/wc-lm-yw-2.txt
python -c 'import wc; wc.combine("outputs/wc-lm-yw-1.txt", "outputs/wc-lm-yw-2.txt")' > outputs/wc-lm-yw-par.txt

CMD="grep -c and"
cat inputs/yellow-full.txt | $CMD > outputs/grep-c-yw-seq.txt
cat inputs/yw-1.txt | $CMD > outputs/grep-c-yw-1.txt
cat inputs/yw-2.txt | $CMD > outputs/grep-c-yw-2.txt
python -c 'import grep_c; grep_c.combine("outputs/grep-c-yw-1.txt", "outputs/grep-c-yw-2.txt")' > outputs/grep-c-yw-par.txt


# python grep.py.combine outputs/out1.txt outputs/out2.txt > outputs/out-par.txt

# grep_c.py
# grep_meta.py
# grep_n.py
# wc.py
