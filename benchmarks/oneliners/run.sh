#!/bin/bash

export SUITE_DIR=$(realpath $(dirname "oneliners"))
export TIMEFORMAT=%R
cd $SUITE_DIR

if [[ "$@" == *"--small"* ]]; then
    scripts_inputs=(
        "grep;1M"
        "nfa-regex;1M"
        "sort;1M"
        "top-n;1M"
        "wf;1M"
        "sort-sort;1M"
        "shortest-scripts;all_cmds"
        "spell;1M"
        "diff;1M"
        "bi-grams;1M"
        "set-diff;1M"
        "set-diff-2;1M"
    )
elif [[ "$@" == *"--test"* ]]; then
    scripts_inputs=(
        "set-diff-2;1M"
        # "shortest-scripts;all_cmdsx100"
    )
elif [[ "$@" == *"--stack_abort"* ]]; then
    scripts_inputs=(
        "wf;1M"
    ) # for debugging
else
    scripts_inputs=(
        "nfa-regex;1G"
        "sort;3G"
        "top-n;3G"
        "wf;3G"
        # "spell;3G"
        # "diff;3G"
        # "bi-grams;3G"
        # "set-diff;3G"
        "sort-sort;3G"
        "shortest-scripts;all_cmdsx100"
    )
fi

dos2unix inputs/1M.txt # TODO: Check if this should match up with the target system

mkdir -p "outputs"
all_res_file="./outputs/oneliners.res"
>$all_res_file

# time_file stores the time taken for each script
# mode_res_file stores the time taken and the script name for every script in a mode (e.g. bash, pash, dish, fish)
# all_res_file stores the time taken for each script for every script run, making it easy to copy and paste into the spreadsheet
oneliners_bash() {
    mkdir -p "outputs/bash"
    mode_res_file="./outputs/bash/oneliners.res"

    echo executing oneliners bash $(date) | tee -a $mode_res_file $all_res_file

    for script_input in "${scripts_inputs[@]}"; do
        IFS=";" read -r -a parsed <<<"${script_input}" # for every item in scripts_input; 0 = script and 1 = input files
        script_file="./scripts/${parsed[0]}.sh"
        chmod +x "$script_file"
        input_file="./inputs/${parsed[1]}.txt"
        output_file="./outputs/bash/${parsed[0]}.out"
        time_file="./outputs/bash/${parsed[0]}.time"
        log_file="./outputs/bash/${parsed[0]}.log"

        { time $script_file "$input_file" >"$output_file"; } 2>"$time_file" #run file with input and direct to output

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

if [[ "$@" == *"--inf"* ]]; then
    set_inf=1
else
    set_inf=0
fi

oneliners_agg() {
    mkdir -p "outputs/agg"

    echo executing oneliners agg $(date) | tee -a $mode_res_file $all_res_file

    for script_input in "${scripts_inputs[@]}"; do
        IFS=";" read -r -a parsed <<<"${script_input}" # for every item in scripts_input; 0 = script and 1 = input files
        script_file="scripts/${parsed[0]}.sh"
        input_file="inputs/${parsed[1]}.txt"
        output_file="./outputs/agg/${parsed[0]}.out"
        time_file="./outputs/agg/${parsed[0]}.time"
        chmod +x ../simple_infra/infra_run.py

        if [[ "$input_file" == *"all_cmds"* && $set_inf == 1 ]]; then
            { time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file; } 2>"$time_file" #run file with input and direct to output
        elif [[ $set_inf == 1 ]]; then
            { time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file -inflate; } 2>"$time_file" #run file with input and direct to output
        else 
            { time ../simple_infra/infra_run.py -n 2 -i $input_file -s $script_file -id $ID -agg $agg_set -o $output_file; } 2>"$time_file" #run file with input and direct to output
        fi

        cat "${time_file}" >>$all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
        ((ID++))
    done
}

oneliners_bash
oneliners_agg
