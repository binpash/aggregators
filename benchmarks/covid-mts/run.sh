#!/bin/bash
benchmark_name=covid-mts
export SUITE_DIR=$(realpath $(dirname $0))
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
all_res_file="./outputs/$benchmark_name.res"
>$all_res_file

covid-mts-bash() {
    mkdir -p "outputs/bash"
    echo executing $benchmark_name bash $(date) | tee -a $all_res_file

    for number in {1..4}; do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_dir="./outputs/bash/$script/"
        output_file="./outputs/bash/$script.out"
        time_file="./outputs/bash/$script.time"

        mkdir -p "$output_dir"

        { time bash "$script_file" "$input_file" >"$output_file"; } 2>"$time_file"
        echo "$input_file $script_file $(cat "$time_file")" | tee -a $all_res_file
    done
}

agg_run=../run-agg.sh 
chmod +x $agg_run 
all_args=$@
covid-mts-agg() {
    mkdir -p "outputs/agg"
    echo executing $benchmark_name agg $(date) | tee -a $all_res_file
    ID=1 # track agg run

    for number in {1..4}; do
        script="${number}"
        script_file="./scripts/$script.sh"
        output_dir="./outputs/bash/$script/"
        output_file="./outputs/bash/$script.out"
        time_file="./outputs/bash/$script.time"

        $agg_run $script_file $input_file $output_file $time_file $ID $benchmark_name $all_res_file "$all_args"
        (( ID++ ))
    done
}

covid-mts-bash
covid-mts-agg
