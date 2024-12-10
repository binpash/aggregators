#!/bin/bash

FULLFILE=$1
shift

OUTPUT_DIR=$1
shift

CMD=$1
shift

AGG=$1
shift

CMD_SPLIT_FILE_DIR="$1"
shift

P=$1
chmod +x $P
shift

FILE_TYPE=".txt"
FILENAME=$(basename "${FULLFILE}") # get filename (hi.txt)
WITHOUTTXT="${FILENAME%.*}"        # get filename without ext. (hi)
CMD_FILE_NAME="${CMD// /-}"        # get command file name append form (grep and -> grep)
CMD_FILE_NAME=$(echo "${CMD}" | awk '{print $1}')

filelist=()
for entry in "$CMD_SPLIT_FILE_DIR"*; do
    filelist+="$entry "
done

output_file=${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}${FILE_TYPE}
time_output=$({ time ${AGG} ${filelist} >$output_file; } 2>&1 >/dev/null)
echo "$output_file, $time_output"
echo "${AGG} ${filelist} > $output_file" >>"${P}" # print to accumulating  file
