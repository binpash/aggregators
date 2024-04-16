#!/bin/bash

mkdir outputs

# make cmd to agg. map to get which cmd should be used
declare -A CMDMAP
CMDMAP["wc"]="s_wc.py"
CMDMAP["grep"]="s_grep.py"
CMDMAP["grep -c"]="s_grep_c.py"

# Global variables
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"
P='./par-execute.sh'
CMDLIST=("wc" "grep and" "grep project" "grep -c Project" "wc -lm" "wc -c")

# Build par execute file
echo '#!/bin/bash' >$P
chmod +x $P

FILE="gb01"
SPLIT_SIZE=2
wget --no-check-certificate 'https://atlas.cs.brown.edu/data/gutenberg/0/1/old/1.txt' -O inputs/${FILE}${FILE_TYPE}

# SAME FOR ALL FILES
split -dl $(($(wc -l <inputs/${FILE}.txt) / SPLIT_SIZE)) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FILE}.txt inputs-s/${FILE}-
# apply command to all split files
for CMD in "${CMDLIST[@]}"; do
    for FILE in "inputs-s/"*; do
        mkfifo int-"${FILE}"
        "cat $CMD ${FILE}" >int-"${FILE}"
    done
    python "$CMD" int-* >${OUTPUT_DIR}"${FILE}"-par.txt
done

# Old piping method, doesn't seem to work but seems more efficient
# IFS=''
# split -dl $(($(wc -l <inputs/${FILE}.txt) / SPLIT_SIZE)) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FILE}.txt |
#     while read -r -d split_file; do
#         wc <"$split_file" >"${OUTPUT_DIR}3-${FILE}${FILE_TYPE}"
#     done
