#!/bin/bash

# ===== SET UP =====

# GLOBAL SETUP
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
SPLIT_DIR="inputs-s/"
FILE_TYPE=".txt"
TESTCOUNT=1

# make relative NEW directories + ensure driver files are executables
rm -rf "${INPUT_DIR%/}"
rm -rf "${OUTPUT_DIR%/}"
rm -rf "${SPLIT_DIR%/}"
mkdir -p "${INPUT_DIR%/}"
mkdir -p "${OUTPUT_DIR%/}"
mkdir -p "${SPLIT_DIR%/}"
chmod +x ./test-seq-driver.sh
chmod +x ./test-par-driver.sh

# Build seq execute file (NOTE: script already ran when running test)
SP='./test-seq-execute.sh' # print ran tests to this file
chmod +x $SP
echo '#!/bin/bash' >$SP
echo '# A record of test (expected value) executed -- sequential command execution alreay ran' >>$SP

# Build par execute file (NOTE: script already ran when running test)
PP='./test-par-execute.sh' # print ran tests to this file
chmod +x $PP
echo '#!/bin/bash' >$PP
echo '# A record of test (actual value) executed -- parallel command execution already ran' >>$PP

# Build evaulation result file
EP="evaluation.txt"
ROWFORMAT=" %-5s | %-20s | %-9s | %-30s | %-15s | %-9s \n" # field width of each content in one row
echo "This test was generated on: $(date +"%Y-%m-%d %H:%M:%S")" >$EP
echo "Check out sequential execution script (input / output) in ${PP}" >>$EP
echo "Check out parallel execution script (input / output) in ${PP}" >>$EP
printf '\n' >>$EP
printf "${ROWFORMAT}" "COUNT" "FILE" "SPLITSIZE" "CMD" "AGG" "CORRECT?" >>$EP
printf "............................................................................................................... \n" >>$EP

# ===== FUNCTIONS =====
# function to invoke sequential driver
seq() {
    ./test-seq-driver.sh "$1" "$2" "$3" "$4" "$5"
    ./test-seq-execute.sh
}

# function to invoke parallel driver
par() {
    ./test-par-driver.sh "$1" "$2" "$3" "$4" "$5" "$6"
    ./test-par-execute.sh
}

# function to find the right agg. given a CMD
find() {
    # Parse CMD out from Flags
    CMD="$(echo "${1}" | cut -d ' ' -f1)"
    FLAG="$(echo "${1}" | cut -d ' ' -f2)"

    # see if we use flags
    if [ "${FLAG:0:1}" = "-" ]; then
        PARSE="$CMD $FLAG"

        # CMD has a flag specific agg
        #   EX: grep -c => grep_c
        RESULT="${CMDMAP["$PARSE"]}"

        # if the agg doesn't have a flag version, return agg without flags
        #   wc -l => wc & wc -lm => wc (share same agg)
        if [ -z "${RESULT}" ]; then
            RESULT=${CMDMAP[${CMD}]}
        fi
    else
        # Don't use flags
        PARSE=$CMD
        RESULT=${CMDMAP[${CMD}]}
    fi

    echo "${RESULT}"
}

# function to get file from URL link or local data directory
# and split read file into even sized separate files given a SPLITSIZE
#   (NOTE: an additional split file will be generated if file cannot be split evenly by SPLITSIZE)
function get_split() {
    local SPLITSIZE=$1
    local URL=$2
    local SAVEFILEAS=$3
    mkdir -p "${SPLIT_DIR}${SAVEFILEAS}"
    if [ ! -e "${URL}" ]; then
        wget --no-check-certificate "${URL}" -O inputs/"${SAVEFILEAS}${FILE_TYPE}"
    else
        cp "${URL}" "${INPUT_DIR}${SAVEFILEAS}${FILE_TYPE}"
    fi
    split -dl $(($(wc -l <"${INPUT_DIR}/${SAVEFILEAS}${FILE_TYPE}") / SPLITSIZE)) -a 2 --additional-suffix=${FILE_TYPE} "${INPUT_DIR}${SAVEFILEAS}${FILE_TYPE}" "${SPLIT_DIR}${SAVEFILEAS}/${SAVEFILEAS}"-
}

function check() {
    FILE=$1
    CMD=$2
    FILENAME=$(basename "${FILE}")                       # get filename (hi.txt)
    WITHOUTTXT="${FILENAME%.*}"                          # get filename without ext. (hi)
    CMD_FILE_NAME="${CMD// /-}"                          # make CMD extension for file name (grep-and)
    SEQ="${WITHOUTTXT}-${CMD_FILE_NAME}-seq${FILE_TYPE}" # build + exec sequential
    PAR="${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}" # build + exec parallel
    if cmp "${OUTPUT_DIR}${SEQ}" "${OUTPUT_DIR}${PAR}"; then
        echo "YES!"
    else
        echo "NO"
    fi
}

# function for main execution
#   1) split given file with given SPLITSIZE
#   2) for every CMD provided in the CMD list,
#       2a) find agg for CMD
#       2b) run seq to produce sequential result for expected output
#       2c) run par to run command on split files and use aggregator to combine result
#       2d) compare expected output (seq) to actual output (par)
#   3) print result of trial by adding a row to the output file
run() {
    local SPLITSIZE=$1
    local URL=$2
    local SAVEFILEAS=$3
    get_split "$SPLITSIZE" "$URL" "$SAVEFILEAS"
    for CMD in "${CMDLIST[@]}"; do
        AGG="$(find "${CMD}")"
        chmod +x "${AGG}"
        FILE=${INPUT_DIR}${SAVEFILEAS}${FILE_TYPE}
        seq "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${SP}"
        par "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${AGG}" "${PP}"
        CORRECT="$(check "${FILE}" "${CMD}")"
        printf "${ROWFORMAT}" $TESTCOUNT "${FILE}" "${SPLITSIZE}" "${CMD}" "${AGG}" "${CORRECT}" >>"${EP}"
        TESTCOUNT=$((TESTCOUNT + 1))
    done
}

# ===== EDIT HERE! =====
# -------------------------------------------------------------
# !!! Edit here to add cmds / aggregators / testing files !!!

CMDLIST=("grep is" "wc -cl" "grep -c hi" "wc" "grep Twentieth" "wc -w -m")
declare -A CMDMAP=(["wc"]="s_wc.py" ["grep"]="s_grep.sh" ["grep -c"]="s_grep_c.py") # Map of aggregators

# Put testing files here:
# SPLITSIZE                         SROUCE                          FILENAME
run 2 data/hi.txt hi
run 8 'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt' gb37
run 2 'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt' gb37II
run 10 'https://atlas.cs.brown.edu/data/gutenberg/7/0/0/0/70000/70000-0.txt' gb70
run 5 'https://atlas.cs.brown.edu/data/gutenberg/7/0/0/0/70001/70001-0.txt' gb71
run 2 'https://atlas.cs.brown.edu/data/gutenberg/7/0/0/0/70002/70002-0.txt' gb72

# -------------------------------------------------------------

printf "...........................................................................................................DONE \n" >>$EP

# Run clean up script to get rid of intermediate files (split files + cmd applied on split files)
#   (NOTE: Comment out if you want to see the intermediate files for debugging!)
chmod +x ./test-clean.sh
./test-clean.sh
