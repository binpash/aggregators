#!/bin/bash

# Global 
mkdir inputs 
INPUT_DIR="inputs/"
FILE_TYPE=".txt"

# Grab file + save as gb.txt
wget --no-check-certificate 'https://atlas.cs.brown.edu/data/gutenberg/0/1/old/1.txt' -O inputs/gb.txt

FILE="gb01"
SPLIT_SIZE=2
split -dl $(($(wc -l < inputs/${FILE}.txt) / SPLIT_SIZE)) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FILE}.txt ${INPUT_DIR}/${FILE}-

# Grab file + save as gb.txt
FILE="gb37"
SPLIT_SIZE=5
wget --no-check-certificate 'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt' -O inputs/${FILE}${FILE_TYPE}
split -dl $(($(wc -l < inputs/${FILE}.txt) / SPLIT_SIZE)) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FILE}.txt ${INPUT_DIR}/${FILE}-
