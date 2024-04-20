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

FILENAME=$(basename "${FULLFILE}") # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"    # get filename without ext. (hi)
CMD_FILE_NAME="${CMD// /-}"

mkdir -p inputs-s-par
mkdir -p "inputs-s-par/${WITHOUTTXT}"
for FILE in inputs-s/${WITHOUTTXT}/*; do
    S_FILENAME=$(basename "${FILE}") # get filename (hi.txt)
    S_WITHOUTTXT="${S_FILENAME%.*}" # get filename without ext. (hi)
    cat ${FILE} | ${CMD} > inputs-s-par/${WITHOUTTXT}/${CMD_FILE_NAME}-${S_WITHOUTTXT}.txt
done
filelist=$(find "inputs-s-par/${WITHOUTTXT}/${CMD_FILE_NAME}-${WITHOUTTXT}"* -type f | sort | tr '\n' ' ')

echo "./${AGG} "${filelist}" > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}" >>$P
"./${AGG}" $filelist > "${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}"
