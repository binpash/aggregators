#!/bin/bash

# Global variables
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"
P='./test-par-execute.sh'
CMDLIST=(wc "grep hi")



# SAME FOR ALL FILES
mkdir inputs-s
split -dl $(($(wc -l <inputs/${FULLFILE}.txt) / SPLIT_SIZE)) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FULLFILE}.txt inputs-s/${FULLFILE}-

# apply command to all split files
for CMD in "${CMDLIST[@]}"; do
    for FILE in inputs-s/*; do
        cat ${FILE} | ${CMD} >a-${FILE}
    done
    chmod +x ./s_"$CMD".py
    filelist=$(ls -1 inputs-s/a-* | tr '\n' ' ')
    echo "# ./s_$CMD.py $filelist > ${OUTPUT_DIR}${FULLFILE}-par.txt" >>$P
    ./s_$CMD.py $filelist >${OUTPUT_DIR}${FULLFILE}-par.txt
    rm -r inputs-s
done
