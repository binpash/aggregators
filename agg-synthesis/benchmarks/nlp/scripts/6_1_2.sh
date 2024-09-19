#!/bin/bash
# tag: uppercase_by_type
# set -e

# Modified original script to test agg specifically 
cat $1 | tr -c 'A-Za-z' '[\n*]' | grep -v "^\s*$" | sort -u | grep -c '^[A-Z]' 

# ORIGINAL
# IN=${IN:-$SUITE_DIR/inputs/pg}
# OUT=${1:-$SUITE_DIR/outputs/6_1_2/}
# ENTRIES=${ENTRIES:-1000}
# mkdir -p "$OUT"

# for input in $(ls ${IN} | head -n ${ENTRIES} | xargs -I arg1 basename arg1)
# do
#     cat $IN/$input | tr -c 'A-Za-z' '[\n*]' | grep -v "^\s*$" | sort -u | grep -c '^[A-Z]' > ${OUT}/${input}.out
# done

# echo 'done';
# rm -rf ${OUT}
