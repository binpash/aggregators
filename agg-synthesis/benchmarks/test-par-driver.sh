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

AGG="../../$1"
shift

P=$1
chmod +x $P
$P
shift

SPLIT_FILELIST="$1"
shift

CMD_SPLIT_FILE_DIR="$1"
shift

IFS=' ' read -r -a split_filelist <<<$SPLIT_FILELIST

FILENAME=$(basename "${FULLFILE}") # get filename (hi.txt)
# WITHOUTTXT="${FILENAME%.*}"        # get filename without ext. (hi)
WITHOUTTXT=$FILENAME
CMD_FILE_NAME="${CMD// /-}" # get command file name append form (grep and -> grep)
CMD_FILE_NAME=$(echo "${CMD}" | awk '{print $1}')

# make intermediate files for cmd applied to files
mkdir -p ${CMD_SPLIT_FILE_DIR}
mkdir -p "${CMD_SPLIT_FILE_DIR}/${WITHOUTTXT}"

# for files in the temporary
filelist=()
for FILE in "${split_filelist[@]}"; do
    S_FILENAME=$(basename "${FILE}") # get filename (hi.txt)
    # S_WITHOUTTXT="${S_FILENAME%.*}"
    S_WITHOUTTXT=$S_FILENAME                                                                                 # get filename without ext. (hi)
    eval "cat "${FILE}" | "${CMD}" > ${CMD_SPLIT_FILE_DIR}/"${WITHOUTTXT}/${CMD_FILE_NAME}-${S_WITHOUTTXT}"" # apply command to all split file
    filelist+="${CMD_SPLIT_FILE_DIR}/${WITHOUTTXT}/${CMD_FILE_NAME}-${S_WITHOUTTXT} "                        # extra space to separate file paths
done
echo "${AGG} ${filelist} > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}"
echo "${AGG} ${filelist} > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}" >>"${P}" # print to accumulating  file
# "./${AGG}" "${filelist}" > "${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}"         # run
