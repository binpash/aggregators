#!/bin/bash
# Find all 2-grams in a piece of text

# . ./scripts/bi-gram.aux.sh

# cat $1 |
#   tr -c 'A-Za-z' '[\n*]' |
#   grep -v "^\s*$" |
#   tr A-Z a-z |
#   bigrams_aux |
#   sort |
#   uniq

# ../scripts/bi-gram.aux.sh # took out main aux function pipeline and replaced it for call to bigrams_aux function

# cat $1 | tr -c 'A-Za-z' '[\n*]' | grep -v "^\s*$" | tee | tail -n +2 | paste | sed '$d' | tr A-Z a-z | sort | uniq

# remove paste for BSD
cat $1 | tr -c 'A-Za-z' '[\n*]' | grep -v "^\s*$" | tee | tail -n +2 | sed '$d' | tr A-Z a-z | sort | uniq
