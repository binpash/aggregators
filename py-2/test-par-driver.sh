#!/bin/bash

# Global variables -- grab from passed-in arguments
FULLFILE=$1
shift

OUTPUT_DIR=$1
shift

FILE_TYPE=$1
shift

CMD=$1
shift 

AGG=$1
chmod +x $AGG
shift 

P=$1
$P

# apply command to all split files
TEMP="inputs-s-par/"
rm -r $TEMP
mkdir inputs-s-par
for FILE in inputs-s/*; do
    FILENAME=$(basename "${FILE}") # get filename (hi.txt)
    WITHOUTTXT="${FILENAME%.*}" # get filename without ext. (hi)
    CMD_FILE_NAME="${CMD// /-}"    # make CMD extension for file name (grep-and)
    cat ${FILE} | ${CMD} > "${TEMP}/${WITHOUTTXT}-${CMD_FILE_NAME}${FILE_TYPE}"
done
filelist=$(ls -1 $TEMP* | tr '\n' ' ')
FILENAME=$(basename "${FULLFILE}") # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"    # get filename without ext. (hi)
CMD_FILE_NAME="${CMD// /-}"
echo "./${AGG} "${filelist}" > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}" >>$P
./${AGG} "${filelist}" > "${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}"

