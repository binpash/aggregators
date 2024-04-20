#!/bin/bash

# GLOBAL SETUP
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
SPLITDIR="inputs-s/"
FILE_TYPE=".txt"

# make relative NEW directories + ensure driver files are executables
rm -rf "${INPUT_DIR%/}"
rm -rf "${OUTPUT_DIR%/}"
rm -rf "${SPLIT_DIR%/}" 
mkdir -p "${INPUT_DIR%/}"
mkdir -p "${OUTPUT_DIR%/}"
mkdir -p "${SPLIT_DIR%/}"
chmod +x ./test-seq-driver.sh
chmod +x ./test-par-driver.sh

# Build seq execute file
SP='./test-seq-execute.sh'
chmod +x $SP
echo '#!/bin/bash' >$SP # print ran tests to this file
echo '# A record of test (expected value) executed -- sequential command execution alreay ran' >>$SP

# Build par execute file
PP='./test-par-execute.sh'
chmod +x $PP
echo '#!/bin/bash' > $PP # print ran tests to this file
echo '# A record of test (actual value) executed -- parallel command execution already ran' >>$PP

# Build evaulation file 
EP="evaluation.txt"
ROWFORMAT="%-20s | %-9s | %-10s | %-20s | %-9s \n"
echo "This test was generated on: $(date +"%Y-%m-%d %H:%M:%S")" > $EP
printf "\n" >> $EP
printf "${ROWFORMAT}" "FILE" "SPLITSIZE" "CMD" "AGG" "CORRECT?">> $EP
printf "............................................................................... \n" >> $EP


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

run() {
    local SPLITSIZE=$1
    local URL=$2
    local SAVEFILEAS=$3
    get_split $SPLITSIZE $URL $SAVEFILEAS
    for CMD in "${CMDLIST[@]}"; do
        AGG="$(find "${CMD}")"
        FILE=${INPUT_DIR}${SAVEFILEAS}${FILE_TYPE}
        seq "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${SP}" 
        par "${FILE}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${AGG}" "${PP}"
        printf "${ROWFORMAT}" "${FILE}" "${SPLITSIZE}" "${CMD}" "${AGG}" >> "${EP}"  
    done
}


# -------------------------------------------------------------
# !! Change here to add cmds / aggregators / testing files !!
CMDLIST=("grep -c hi" "wc" "grep and" "wc -lm") 
CMDLIST=("wc" "grep hi" "wc -l" "grep -c hi")
declare -A CMDMAP=(["wc"]="s_wc.py" ["grep"]="s_grep.py" ["grep -c"]="s_grep_c.py")

#  SPLITSIZE                         SROUCE                                  FILENAME   
run    8    'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt'    gb37  
run    2    'https://atlas.cs.brown.edu/data/gutenberg/3/7/9/3790/3790.txt'    gb37II 

# -------------------------------------------------------------

# Run clean up script to get rid of intermediate files 
chmod +x ./test-eval-clean.sh
./test-eval-clean.sh

