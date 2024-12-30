#!/bin/bash

script_file=$1
input_file=$2
output_file=$3
time_file=$4
ID=$5
benchmark=$6
all_res_file=$7

export SUITE_DIR=$(realpath $(dirname $benchmark))
export TIMEFORMAT=%R
cd $SUITE_DIR

# Set which aggregators we are using.
if [[ "$@" == *"--all"* ]]; then
    agg_set=all
elif [[ "$@" == *"--lean"* ]]; then
    agg_set=lean
else
    agg_set=python
fi

# Set if we need input inflation between stages.
if [[ "$@" == *"-inf"* && "$input_file" == *".txt" ]]; then
    set_inf=1
else
    set_inf=0
fi

# Set if we want to use random input between every stage.
if [[ "$@" == *"-rand"* && "$input_file" == *".txt" ]]; then
    set_rand=1
else
    set_rand=0
fi

input_configs=""
if [[ $set_inf == 1 ]]; then
    input_configs+="-inflate "
fi

if [[ "$input_file" == *"all_cmds"* && $set_inf == 1 ]]; then
    input_configs=""
fi

if [[ $set_rand == 1 ]]; then
    target_bytes=$(echo "$@" | awk -v RS=' ' '/-random/ {getline; print}')
    input_configs+="-random $target_bytes"
fi

echo $input_configs >&2

# Run aggregator with configurations.
{ time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file $input_configs; } 2>"$time_file"

echo "$input_file $script_file $(cat "$time_file")" | tee -a $all_res_file
