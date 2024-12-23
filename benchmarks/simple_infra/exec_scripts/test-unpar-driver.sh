#!/bin/bash

# Global variables -- grab from passed-in arguments

FILE=$1

OUTPUT_DIR=$2

CMD=$3

FILE_TYPE=".txt"
FILENAME=$(basename "${FILE}") # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"    # get filename without ext. (hi)
# CMD_FILE_NAME="${CMD// /-}"
CMD_FILE_NAME=$(echo "${CMD}" | awk '{print $1}') # make CMD extension for file name (grep-and)
OUTPUT_FILE=${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}${FILE_TYPE}

if [ ! -f $FILE ]; then
    echo $FILE " don't exists"
fi

executed="cat ${FILE} | cat > $OUTPUT_FILE"
time_output=$({ time eval "$executed"; } 2>&1 >/dev/null)
printf '%s\n%s\n%s\n' "$executed" "$OUTPUT_FILE" "$time_output"
