#!/bin/bash

# Global variables -- grab from passed-in arguments

INPUT_DIR=$1
shift

OUTPUT_DIR=$1
shift

FILE_TYPE=$1
shift

CMDLIST=("$@")

# Build seq execute file
P='./test-seq-execute.sh'
echo '#!/bin/bash' >$P # print ran tests to this file
echo '# Already executed -- records down what was exectued' >>$P
chmod +x $P

for CMD in "${CMDLIST[@]}"; do
    for FILE in "$INPUT_DIR"*; do
        FILENAME=$(basename "${FILE}") # get filename (hi.txt)
        WITHOUTTXT="${FILENAME%.*}"    # get filename without ext. (hi)
        CMD_FILE_NAME="${CMD// /-}"    # make CMD extension for file name (grep-and)
        echo "cat ${FILE} | $CMD > ${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-seq${FILE_TYPE}" >>$P
        cat "${FILE}" | $CMD >"${OUTPUT_DIR}${WITHOUTTXT}-${CMD_FILE_NAME}-seq${FILE_TYPE}" # execute seq output
    done
done
