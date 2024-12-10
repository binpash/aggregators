#!/bin/bash

# Global variables -- grab from passed-in arguments

FILE=$1
shift

OUTPUT_DIR=$1
shift

CMD=$1
shift

FILE_TYPE=".txt"
FILENAME=$(basename "${FILE}") # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"    # get filename without ext. (hi)
# CMD_FILE_NAME="${CMD// /-}"
CMD_FILE_NAME=$(echo "${CMD}" | awk '{print $1}') # make CMD extension for file name (grep-and)
OUTPUT_FILE=${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}${FILE_TYPE}

if [ ! -f $FILE ]; then
    echo $FILE " don't exists"
fi

executed="cat ${FILE} | $CMD > $OUTPUT_FILE"
time_output=$({ time eval "$executed"; } 2>&1 >/dev/null)
echo "$executed,$OUTPUT_FILE,$time_output"
