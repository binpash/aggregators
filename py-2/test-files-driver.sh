#!/bin/bash

INPUT_DIR=$1
shift

FILE_TYPE=$1

SPLITDIR="inputs-s/"
mkdir -p inputs-s
function get_split() {
    local SPLITSIZE=$1
    local URL=$2
    local SAVEFILEAS=$3
    mkdir -p "${SPLITDIR}${SAVEFILEAS}"
    if [ ! -e $URL ]; then 
        wget --no-check-certificate "${URL}" -O inputs/${SAVEFILEAS}${FILE_TYPE} 
    else 
        cp $URL ${INPUT_DIR}${SAVEFILEAS}${FILE_TYPE}
    fi
    split -dl $(($(wc -l < "${INPUT_DIR}/${SAVEFILEAS}${FILE_TYPE}") / ${SPLITSIZE})) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${SAVEFILEAS}.txt ${SPLITDIR}${SAVEFILEAS}/${SAVEFILEAS}-
}

# Grab file + save as gb.txt
get_split 8 'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt' gb37  
get_split 2 'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt' "gb37II" 
get_split 3 ./data/novel_long.txt "nl"


