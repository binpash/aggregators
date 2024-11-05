#!/bin/bash

export TIMEFORMAT=%R

script_file=./$1
chmod +x "$script_file"
input_file=./$2
log_file=$3

script_base_w_ext=$(basename "${script_file}") # get filename (hi.txt)
script_base="${script_base_w_ext%.*}"

dos2unix inputs/1M.txt # TODO: Check if this should match up with the target system
dos2unix inputs/small_text.txt
dos2unix inputs/special_char.txt

mkdir -p "outputs"

# time_file stores the time taken for each script
# mode_res_file stores the time taken and the script name for every script in a mode (e.g. bash, pash, dish, fish)
# all_res_file stores the time taken for each script for every script run, making it easy to copy and paste into the spreadsheet
oneliners_bash() {
    mkdir -p "outputs/bash"
    # mode_res_file="./outputs/bash/oneliners.res"
    output_file="./outputs/bash/${script_base}.out"
    time_file="./outputs/bash/${script_base}.time"
    # log_file="./outputs/bash/${script_base}.log"

    echo executing $script_file bash $(date) | tee -a $mode_res_file $all_res_file
    { time $script_file "$input_file" >"$output_file"; } 2>"$time_file" #run file with input and direct to output
    echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
}

ID=1 # track agg run

# run the onliner suite using aggregators
oneliners_agg() {
    time_file="./outputs/agg/${script_base}.time"
    log_file=$log_file
    agg_exec_file="./agg-steps/agg-${script_base}.sh"
    output_file="./outputs/agg/${script_base}.out"
    AGG_FILE="./agg_run.sh"
    chmod +x $AGG_FILE
    mkdir -p "outputs/agg"
    mkdir -p "agg-steps"
    # mode_res_file="./outputs/bash/oneliners.res"

    echo executing $script_file agg $(date) | tee -a $mode_res_file $all_res_file
    { time ./agg_run.sh "$script_file" "$input_file" $ID "$log_file" "$agg_exec_file" >"$output_file"; } 2>"$time_file" #run file with input and direct to output
    echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
    ((ID++))
}

# "./outputs/agg/${script_base}.log"

oneliners_bash
oneliners_agg
