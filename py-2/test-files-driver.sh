#!/bin/bash

INPUT_DIR=$1
shift

SPLIT_DIR=$1 
shift 

FILE_TYPE=$1

function get_split() {
    SPLITSIZE=$1
    URL=$2
    SAVEFILEAS=$3
    if [ ! -e $URL ]; then 
        wget --no-check-certificate "${URL}" -O inputs/${SAVEFILEAS}${FILE_TYPE}
    else 
        cp $URL ${INPUT_DIR}${SAVEFILEAS}${FILE_TYPE}
    fi
    split -dl $(($(wc -l < inputs/${SAVEFILEAS}.txt) / ${SPLITSIZE})) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${SAVEFILEAS}.txt ${SPLIT_DIR}/${SAVEFILEAS}-
}

# Grab file + save as gb.txt
# get_split 8 'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt' gb37
get_split 2 'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt' "gb37II"
# get_split 3 ./data/novel_long.txt "nl"