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
        "grep;test"
        "nfa-regex;test"
        "top-n;test"
        "sort;test"
        "wf;test"
        "sort-sort;test"
    )
elif [[ "$@" == *"--single"* ]]; then
    scripts_inputs=(
        "bi-grams;1M"
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

dos2unix inputs/1M.txt

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

# run the onliner suite using aggregators
oneliners_agg() {
    AGG_FILE="../agg_run.sh"
    chmod +x $AGG_FILE
    mkdir -p "outputs/agg"

    echo executing oneliners agg $(date) | tee -a $mode_res_file $all_res_file
    for script_input in "${scripts_inputs[@]}"; do
        IFS=";" read -r -a parsed <<<"${script_input}" # for every item in scripts_input; 0 = script and 1 = input files
        script_file="./scripts/${parsed[0]}.sh"
        input_file="./inputs/${parsed[1]}.txt"
        output_file="./outputs/agg/${parsed[0]}.out"
        time_file="./outputs/agg/${parsed[0]}.time"
        log_file="./outputs/agg/${parsed[0]}.log"
        { time ../agg_run.sh "$script_file" "$input_file" $ID oneliners >"$output_file"; } 2>"$time_file" #run file with input and direct to output

        cat "${time_file}" >>$all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
        ((ID++))
    done
}

oneliners_bash
oneliners_agg
