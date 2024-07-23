#!/bin/bash

export SUITE_DIR=$(realpath $(dirname "$0"))
export TIMEFORMAT=%R
cd $SUITE_DIR

if [[ "$1" == "--small" ]]; then
    echo "Using small input"
    input_file="$SUITE_DIR/inputs/in_small.csv"
else
    echo "Using default input"
    input_file="$SUITE_DIR/inputs/in.csv"
fi

mkdir -p "outputs"
all_res_file="./outputs/covid-mts.res"
> $all_res_file

# time_file stores the time taken for each script
# mode_res_file stores the time taken and the script name for every script in a mode (e.g. bash, pash, dish, fish)
# all_res_file stores the time taken for each script for every script run, making it easy to copy and paste into the spreadsheet
covid-mts_bash() {
    mkdir -p "outputs/bash"
    mode_res_file="./outputs/bash/covid-mts.res"
    > $mode_res_file

    echo executing covid-mts bash $(date) | tee -a $mode_res_file $all_res_file

    for number in `seq 4` ## initial: FIXME 5.sh is not working yet
    do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_dir="./outputs/bash/$script/"
        output_file="./outputs/bash/$script.out"
        time_file="./outputs/bash/$script.time"
        log_file="./outputs/bash/$script.log"

        time bash $script_file $input_file > $output_file  2> $time_file

        cat "${time_file}" >> $all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
    done
}

covid-mts_agg() {
    AGG_FILE="../agg_run.sh"
    chmod +x $AGG_FILE
    mkdir -p "outputs/agg"
    # mode_res_file="./outputs/agg/oneliners.res"
    # > $mode_res_file
    
    echo executing oneliners agg $(date) | tee -a $mode_res_file $all_res_file

    for number in `seq 3`
    do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_dir="./outputs/agg/$script/"
        output_file="./outputs/agg/$script.out"
        time_file="./outputs/agg/$script.time"
        log_file="./outputs/agg/$script.log"
        { time ../agg_run.sh $script_file $input_file oneliners > $output_file; } 2> $time_file #run file with input and direct to output
        
        cat "${time_file}" >> $all_res_file
        echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
    done
    # since scripts are similar, remove interm. files once to ensure script 4 does not use previous script interm. 
    rm -r inputs-s
    script_file="./scripts/4.sh"
    output_dir="./outputs/agg/4/"
    output_file="./outputs/agg/4.out"
    time_file="./outputs/agg/4.time"
    log_file="./outputs/agg/4.log"
    { time ../agg_run.sh $script_file $input_file oneliners > $output_file; } 2> $time_file #run file with input and direct to output
    cat "${time_file}" >> $all_res_file
    echo "$script_file $(cat "$time_file")" | tee -a $mode_res_file
}

covid-mts_bash
covid-mts_agg
