#!/bin/bash

# Global variables -- grab from passed-in arguments

FILE=$1
shift

OUTPUT_DIR=$1
shift

CMD=$1
shift

P=$1

FILE_TYPE=".txt"
FILENAME=$(basename "${FILE}") # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"    # get filename without ext. (hi)
# CMD_FILE_NAME="${CMD// /-}"
CMD_FILE_NAME=$(echo "${CMD}" | awk '{print $1}') # make CMD extension for file name (grep-and)
OUTPUT_FILE=${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}${FILE_TYPE}

if [ ! -f $FILE ]; then
    echo $FILE " don't exists"
fi

time_output=$({ time cat $FILE | $CMD >$OUTPUT_FILE; } 2>&1 >/dev/null)
echo "$OUTPUT_FILE, $time_output"
echo "cat ${FILE} | $CMD > $OUTPUT_FILE" >>"${P}" # print seq to accumulating file
