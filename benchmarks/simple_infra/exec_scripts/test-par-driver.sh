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
executed="${AGG} ${filelist} > $output_file"
time_output=$({ time eval "$executed"; } 2>&1 >/dev/null)
printf '%s\n%s\n%s\n' "$executed" "$output_file" "$time_output"
# echo "$executed,$output_file,$time_output"
