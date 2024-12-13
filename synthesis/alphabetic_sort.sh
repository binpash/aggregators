#!/bin/bash
# This script sorts the characters of the input string alphabetically
while read input; do
    echo "$input" | grep -o . | sort | tr -d '\n'
done
