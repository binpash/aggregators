#!/bin/bash
export SUITE_DIR=$(realpath $(dirname "$0"))
export TIMEFORMAT=%R
cd $SUITE_DIR

if [[ "$1" == "--small" ]]; then
    echo "Using small input"
    export INPUT="$SUITE_DIR/inputs/access.log"
else
    # not using this
    echo "Using default input"
    export IN="$SUITE_DIR/inputs/pg"
fi

# ////////
# original script
# REPO_TOP=$(git rev-parse --show-toplevel)

# eval_dir="${REPO_TOP}/analysis-logs"
# results_dir="${eval_dir}/results"
# inputs_dir="${eval_dir}/input"

# shell="/bin/bash"

# mkdir -p $results_dir

# export INPUT=${inputs_dir}/access.log
# script="${eval_dir}/nginx.sh"

# echo "Executing $(basename "$script")"
# $shell "$script" > "$results_dir/$(basename "$script").out"

# ////////

covid-mts_bash() {
for number in $(
        seq 7
    ); do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_dir="./outputs/bash/$script/"
        output_file="./outputs/bash/$script.out"
        time_file="./outputs/bash/$script.time"
        log_file="./outputs/bash/$script.log"

        time bash $script_file $input_file >$output_file 2>$time_file

        cat "${time_file}" >>$all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
    done
}

ID=1 # track agg run

covid-mts_agg() {
    AGG_FILE="../agg_run.sh"
    chmod +x $AGG_FILE
    mkdir -p "outputs/agg"
    echo executing oneliners agg $(date) | tee -a $mode_res_file $all_res_file

    for number in $(seq 7); do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_dir="./outputs/agg/$script/"
        output_file="./outputs/agg/$script.out"
        time_file="./outputs/agg/$script.time"
        log_file="./outputs/agg/$script.log"
        { time ../agg_run.sh $script_file $input_file $ID covid-mts >$output_file; } 2>$time_file #run file with input and direct to output

        cat "${time_file}" >>$all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
        ((ID++))
    done
}

covid-mts_bash
covid-mts_agg
