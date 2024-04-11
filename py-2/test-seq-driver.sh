#!/bin/bash

mkdir outputs

# Global variables
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"
P='./seq-execute.sh'
CMDLIST=("wc" "grep and" "grep project" "grep -c Project" "wc -lm" "wc -c")

# Build seq execute file
echo '#!/bin/bash' >$P
chmod +x $P

for CMD in "${CMDLIST[@]}"; do
    for FILE in "$INPUT_DIR"*; do
        FILENAME=$(basename ${FILE})
        WITHOUTTXT="${FILENAME%.*}"
        CMD_FILE_NAME="${CMD// /-}"
        echo "cat "${FILE}" | $CMD > "${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-seq${FILE_TYPE}"" >>$P
    done
done
