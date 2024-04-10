#!/bin/bash

mkdir inputs 
INPUT_DIR="inputs/"
FILE_TYPE=".txt"

# Grab file + save as gb.txt
wget -P inputs --no-check-certificate 'https://atlas.cs.brown.edu/data/gutenberg/0/1/old/1.txt' -O gb.txt

FILE="gb"
SPLIT_SIZE=2
split -l $(($(wc -l < inputs/yw.txt) / SPLIT_SIZE)) -a -d 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FILE}.txt ${INPUT_DIR}/${FILE}- 