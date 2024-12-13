#!/bin/bash

cat $1 | awk '($9 ~ /404/)' ${INPUT} | awk '{print $7}' | sort | uniq -c | sort -rn
