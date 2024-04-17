#!/bin/bash

# GLOBAL SETUP
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"

# make cmd to agg. map to get which cmd should be used
# !! Change here to add cmds or aggregators !!
CMDLIST=("wc" "grep and")
declare -A CMDMAP=(["wc"]="s_wc.py" ["grep"]="s_grep.py")

# make relative directories + ensure driver files are executables
mkdir -p "${INPUT_DIR%/}"
mkdir -p "${OUTPUT_DIR%/}"
chmod +x ./test-seq-driver.sh
chmod +x ./test-par-driver.sh

# function to invoke sequential driver
seq() {
    ./test-seq-driver.sh "${INPUT_DIR}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMDLIST[@]}"
}

# function to invoke parallel driver
# par() {
#     ./test-par-driver.sh "${INPUT_DIR}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMDLIST[@]}"
# }

# function to find the right agg. given a CMD
find() {
    echo "${CMDMAP[wc]}"
    return
}

# Main loop for generating seq + par result with each cmd in the cmd list
# for CMD in "${CMDLIST[@]}"; do
#     for FILE in "${INPUT_DIR}"*; do
#         seq "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}"
#         par "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${AGG}"
#     done
# done

find
