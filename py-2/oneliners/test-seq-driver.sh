#!/bin/bash

# Global variables -- grab from passed-in arguments

FILE=$1
shift

OUTPUT_DIR=$1
shift

FILE_TYPE=$1
shift

CMD=$1
shift

P=$1

FILENAME=$(basename "${FILE}")                                                                   # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"                                                                      # get filename without ext. (hi)
# CMD_FILE_NAME="${CMD// /-}"   
CMD_FILE_NAME=$(echo ${CMD} | awk '{print $1}')                                                                  # make CMD extension for file name (grep-and)
echo "cat ${FILE} | $CMD > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-seq${FILE_TYPE}"
echo "cat ${FILE} | $CMD > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-seq${FILE_TYPE}" >> "${P}" # print seq to accumulating file
# cat "${FILE}" | $CMD >"${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-seq${FILE_TYPE}"              # execute seq output
