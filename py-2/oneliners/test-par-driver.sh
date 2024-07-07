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

AGG="../$1"
chmod +x $AGG
shift

P=$1
chmod +x $P
$P
shift 

SPLIT_FILELIST="$1"
shift

IFS=' ' read -r -a split_filelist <<< $SPLIT_FILELIST

FILENAME=$(basename "${FULLFILE}") # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"        # get filename without ext. (hi)
CMD_FILE_NAME="${CMD// /-}"        # get command file name append form (grep and -> grep-and)

# make intermediate files for cmd applied to files
mkdir -p inputs-s-par
mkdir -p "inputs-s-par/${WITHOUTTXT}"

# for files in the temporary
filelist=()
for FILE in "${split_filelist[@]}"; do
    echo $FILE >> hi2.txt
    S_FILENAME=$(basename "${FILE}")                                                          # get filename (hi.txt)
    S_WITHOUTTXT="${S_FILENAME%.*}"                                                           # get filename without ext. (hi)
    cat "${FILE}" | ${CMD} > inputs-s-par/"${WITHOUTTXT}/${CMD_FILE_NAME}-${S_WITHOUTTXT}.txt" # apply command to all split file
    filelist+="inputs-s-par/${WITHOUTTXT}/${CMD_FILE_NAME}-${S_WITHOUTTXT}.txt "
done

echo "${AGG} ${filelist} > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}"
echo "${AGG} ${filelist} > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}" >>"${P}" # print to accumulating  file
# "./${AGG}" "${filelist}" > "${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-par${FILE_TYPE}"         # run
