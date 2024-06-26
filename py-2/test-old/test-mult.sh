#!/bin/bash

# Global 
mkdir outputs
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"

# Command specific 
CMD="wc"
INPUT_FILE1="yw"
INPUT_FILE2="ms"
OUTPUT_FILE="wc-yw-ms"
PY_COMB="python m_wc.py"
$CMD "${INPUT_DIR}${INPUT_FILE1}${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-seq${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-1${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-1${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-2${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-2${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE}"
${PY_COMB} ${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE} ${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE} > "${OUTPUT_DIR}${OUTPUT_FILE}-par${FILE_TYPE}"


CMD="wc -l"
INPUT_FILE1="yw"
INPUT_FILE2="ms"
OUTPUT_FILE="wc-l-yw-ms"
PY_COMB="python m_wc.py"
$CMD "${INPUT_DIR}${INPUT_FILE1}${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-seq${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-1${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-1${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-2${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-2${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE}"
${PY_COMB} ${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE} ${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE} > "${OUTPUT_DIR}${OUTPUT_FILE}-par${FILE_TYPE}"


CMD="wc -lc"
INPUT_FILE1="yw"
INPUT_FILE2="ms"
OUTPUT_FILE="wc-lc-yw-ms"
PY_COMB="python m_wc.py"
$CMD "${INPUT_DIR}${INPUT_FILE1}${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-seq${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-1${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-1${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-2${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-2${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE}"
${PY_COMB} ${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE} ${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE} > "${OUTPUT_DIR}${OUTPUT_FILE}-par${FILE_TYPE}"


CMD="grep and"
INPUT_FILE1="yw"
INPUT_FILE2="ms"
OUTPUT_FILE="grep-yw-ms"
PY_COMB="python m_grep.py"
FILE_LIST="full ${INPUT_DIR}${INPUT_FILE1}${FILE_TYPE} ${INPUT_DIR}${INPUT_FILE2}${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-seq${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-1${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-1${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-2${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-2${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE}"
${PY_COMB} ${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE} ${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE} ${FILE_LIST} > "${OUTPUT_DIR}${OUTPUT_FILE}-par${FILE_TYPE}"

CMD="grep -c Project"
INPUT_FILE1="yw"
INPUT_FILE2="ms"
OUTPUT_FILE="grep-c-yw-ms"
PY_COMB="python m_grep_c.py"
$CMD "${INPUT_DIR}${INPUT_FILE1}${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-seq${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-1${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-1${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-2${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-2${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE}"
${PY_COMB} ${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE} ${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE} > "${OUTPUT_DIR}${OUTPUT_FILE}-par${FILE_TYPE}"