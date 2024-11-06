#!/bin/bash

export SUITE_DIR=$(realpath $(dirname "$0"))
export TIMEFORMAT=%R
cd "$SUITE_DIR" || exit

if [[ "$1" == "--small" ]]; then
    echo "Using small input"
    input_file="$SUITE_DIR/inputs/in_small.csv"
else
    echo "Using default input"
    input_file="$SUITE_DIR/inputs/in.csv"
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

covid-mts_agg() {
    AGG_FILE="../agg_run.sh"
    chmod +x $AGG_FILE
    mkdir -p "outputs/agg"
    mkdir -p "agg-steps"

    echo executing oneliners agg $(date) | tee -a $mode_res_file $all_res_file
    cmd_instance_counter="cmd_instance_num.txt"

    for number in $(seq 4); do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_file="./outputs/agg/$script.out"
        time_file="./outputs/agg/$script.time"
        log_file="./outputs/agg/$script.log"
        agg_exec_file="./agg-steps/agg-$script.sh"
        { time ../agg_run.sh "$script_file" "$input_file" $ID "$log_file" "$agg_exec_file" "$cmd_instance_counter" >"$output_file"; } 2>"$time_file" #run file with input and direct to output

        cat "${time_file}" >>$all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
        ((ID++))
    done
}

covid-mts_bash
covid-mts_agg
