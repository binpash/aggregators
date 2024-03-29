#!/bin/bash

# Global 
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs-mult/"
FILE_TYPE=".txt"

# Command specific 
CMD="grep and"
INPUT_FILE1="yw"
INPUT_FILE2="ms"
OUTPUT_FILE="grep-yw-ms"
PY_COMB=""
$CMD "${INPUT_DIR}${INPUT_FILE1}${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-seq${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-1${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-1${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-1${FILE_TYPE}"
$CMD "${INPUT_DIR}${INPUT_FILE1}-2${FILE_TYPE}" "${INPUT_DIR}${INPUT_FILE2}-2${FILE_TYPE}" > "${OUTPUT_DIR}${OUTPUT_FILE}-2${FILE_TYPE}"
# python -c 'import grep; grep.m_combine("outputs/grep-yw-ms-1.txt", "outputs/grep-yw-ms-2.txt", [inputs/yw.txt, inputs/ms.txt])' > outputs/grep-yw-ms.txt