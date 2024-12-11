#!/bin/bash

export SUITE_DIR=$(realpath $(dirname "covid-mts"))
export TIMEFORMAT=%R
cd "$SUITE_DIR" || exit

if [[ "$1" == "--small" ]]; then
    echo "Using small input"
    input_file="inputs/in_small.csv"
else
    echo "Using default input"
    input_file="inputs/in.csv"
fi

mkdir -p "outputs"
all_res_file="./outputs/covid-mts.res"

# time_file stores the time taken for each script
# mode_res_file stores the time taken and the script name for every script in a mode (e.g. bash, pash, dish, fish)
# all_res_file stores the time taken for each script for every script run, making it easy to copy and paste into the spreadsheet
covid-mts_bash() {
    mkdir -p "outputs/bash"
    mode_res_file="./outputs/bash/covid-mts.res"

    echo executing covid-mts bash "$(date)" | tee -a $mode_res_file $all_res_file

    for number in $( ## initial: FIXME 5.sh is not working yet
        seq 4
    ); do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_dir="./outputs/bash/$script/"
        output_file="./outputs/bash/$script.out"
        time_file="./outputs/bash/$script.time"
        log_file="./outputs/bash/$script.log"

        time bash "$script_file" "$input_file" >"$output_file" 2>"$time_file"

        cat "${time_file}" >>$all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
    done
}

ID=1 # track agg run
if [[ "$@" == *"--all"* ]]; then
    agg_set=all
elif [[ "$@" == *"--lean"* ]]; then
    agg_set=lean
else
    agg_set=python
fi
covid-mts_agg() {
    echo executing oneliners agg $(date) | tee -a $mode_res_file $all_res_file
    mkdir -p ./outputs/agg
    for number in $(seq 4); do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_file="./outputs/agg/$script.out"
        time_file="./outputs/agg/$script.time"
        chmod +x ../simple_infra/infra_run.py
        { time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file; } 2>"$time_file" #run file with input and direct to output
        cat "${time_file}" >>$all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
        ((ID++))
    done
}

covid-mts_bash
covid-mts_agg
