#!/bin/bash
benchmark_name=oneliners
export SUITE_DIR=$(realpath $(dirname $0))
export TIMEFORMAT=%R
cd "$SUITE_DIR" || exit

if [[ "$@" == *"--small"* ]]; then
    echo "Using small input"
    scripts_inputs=(
        "grep;1M"
        "nfa-regex;1M"
        "sort;1M"
        "top-n;1M"
        "wf;1M"
        "sort-sort;1M"
        # "shortest-scripts;all_cmds" # Removed from most updated: https://github.com/binpash/benchmarks/tree/main/oneliners/scripts
        "spell;1M"
        "diff;1M"
        "bi-grams;1M"
        "set-diff;1M"
        "set-diff-2;1M"
    )
elif [[ "$@" == *"--test"* ]]; then
    echo "Using test debugging input"
    scripts_inputs=(
        "single;1M"
        # "shortest-scripts;all_cmdsx100"
    )
else
    echo "Using default input"
    scripts_inputs=(
        "grep;3G"
        "nfa-regex;3G"
        "sort;3G"
        "top-n;3G"
        "wf;3G"
        "sort-sort;3G"
        # "shortest-scripts;all_cmdsx100"
        "spell;3G"
        "diff;3G"
        "bi-grams;3G"
        "set-diff;3G"
        "set-diff-2;3G"
    )
fi

dos2unix inputs/1M.txt # TODO: Check if this should match up with the target system

mkdir -p "outputs"
all_res_file="./outputs/$benchmark_name.res"
>$all_res_file

oneliners_bash() {
    mkdir -p "outputs/bash"
    echo executing $benchmark_name bash $(date) | tee -a $all_res_file

    for script_input in "${scripts_inputs[@]}"; do
        IFS=";" read -r -a parsed <<<"${script_input}"
        script_file="./scripts/${parsed[0]}.sh"
        chmod +x "$script_file"
        input_file="./inputs/${parsed[1]}.txt"
        output_file="./outputs/bash/${parsed[0]}.out"
        time_file="./outputs/bash/${parsed[0]}.time"

        { time $script_file "$input_file" >"$output_file"; } 2>"$time_file" #run file with input and direct to output
        echo "$input_file $script_file $(cat "$time_file")" | tee -a $all_res_file
    done
}

agg_run=../run-agg.sh
chmod +x $agg_run
all_args=$@
oneliners_agg() {
    mkdir -p "outputs/agg"
    echo executing $benchmark_name agg $(date) | tee -a $all_res_file
    ID=1 # track agg run

    for script_input in "${scripts_inputs[@]}"; do
        IFS=";" read -r -a parsed <<<"${script_input}"
        script_file="./scripts/${parsed[0]}.sh"
        chmod +x "$script_file"
        input_file="./inputs/${parsed[1]}.txt"
        output_file="./outputs/bash/${parsed[0]}.out"
        time_file="./outputs/bash/${parsed[0]}.time"

        $agg_run $script_file $input_file $output_file $time_file $ID $benchmark_name $all_res_file "$all_args"
        ((ID++))
    done
}

oneliners_bash
oneliners_agg
