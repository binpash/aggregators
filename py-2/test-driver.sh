#!/bin/bash

# GLOBAL SETUP
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"

# make relative directories + ensure driver files are executables
mkdir -p "${INPUT_DIR%/}"
mkdir -p "${OUTPUT_DIR%/}"
chmod +x ./test-files-driver.sh 
chmod +x ./test-seq-driver.sh
chmod +x ./test-par-driver.sh

# -------------------------------------------------------------
# !! Change here to add cmds / aggregators / testing files !!
CMDLIST=("grep -c hi" "wc" "grep and" "wc -lm") 
declare -A CMDMAP=(["wc"]="s_wc.py" ["grep"]="s_grep.py" ["grep -c"]="s_grep_c.py")
./test-files-driver.sh 
# -------------------------------------------------------------

# Build seq execute file
SP='./test-seq-execute.sh'
chmod +x $SP
echo '#!/bin/bash' >$SP # print ran tests to this file
echo '# Already executed -- records down what was exectued' >>$SP

# Build par execute file
PP='./test-par-execute.sh'
chmod +x $PP
echo '#!/bin/bash' > $PP # print ran tests to this file
echo '# Already executed -- records down what was exectued' >>$PP


# function to invoke sequential driver
seq() {
    ./test-seq-driver.sh "$1" "$2" "$3" "$4" "$5"
}

# function to invoke parallel driver
par() {
    ./test-par-driver.sh "$1" "$2" "$3" "$4" "$5" "$6"
}

# function to find the right agg. given a CMD
# wc -l -> wc, wc -> wc 
# grep -c -> grep -c 
find() {
    CMD="$(echo ${1} | cut -d ' ' -f1)" 
    FLAG="$(echo ${1} | cut -d ' ' -f2)" 
    # see if we use flag
    if [ "${FLAG:0:1}" = "-" ]; then
        PARSE="$CMD $FLAG"
        RESULT="${CMDMAP["$PARSE"]}"
        if [ -z $RESULT ]; then 
            RESULT=${CMDMAP[${CMD}]}
        fi
    else
        PARSE=$CMD 
        RESULT=${CMDMAP[${CMD}]}
    fi
    echo $RESULT 
}

# Main loop for generating seq + par result with each cmd in the cmd list
for CMD in "${CMDLIST[@]}"; do
    AGG="$(find "${CMD}")"
    for FILE in "${INPUT_DIR}"*; do
        seq "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${SP}"
        par "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${AGG}"
    done
done
