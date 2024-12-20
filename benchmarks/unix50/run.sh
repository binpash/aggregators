#!/bin/bash
benchmark_name=unix50
export SUITE_DIR=$(realpath $(dirname $0))
export TIMEFORMAT=%R
cd $SUITE_DIR || exit

if [[ "$@" == *"--small"* ]]; then
    echo "Using small input"
    scripts_inputs=(
        "1;1"
        "2;1"
        "3;1"
        "4;1"
        "5;2"
        "6;3"
        "7;4"
        "8;4"
        "9;4"
        "10;4"
        "11;4"
        "12;4"
        "13;5"
        "14;6"
        "15;7"
        "16;7"
        "17;7"
        "18;8"
        "19;8"
        "20;8"
        "21;8"
        # "22;8_1M"
        "23;9.1"
        "24;9.2"
        "25;9.3"
        "26;9.4"
        # "27;9.5_1M"
        "28;9.6"
        "29;9.7"
        "30;9.8"
        "31;9.9"
        "32;10"
        "33;10"
        "34;10"
        "35;11"
        "36;11"
    )
elif [[ "$@" == *"--test"* ]]; then
    echo "Using test debugging input"
    scripts_inputs=(
        "4;1"
    ) # for debugging
else
    echo "Using default input"
    scripts_inputs=(
        "1;1_3G"
        "2;1_3G"
        "3;1_3G"
        "4;1_3G"
        "5;2_3G"
        "6;3_3G"
        "7;4_3G"
        "8;4_3G"
        "9;4_3G"
        "10;4_3G"
        "11;4_3G"
        "12;4_3G"
        "13;5_3G"
        "14;6_3G"
        "15;7_3G"
        "16;7_3G"
        "17;7_3G"
        "18;8_3G"
        "19;8_3G"
        "20;8_3G"
        "21;8_3G"
        # "22;8_3G"
        "23;9.1_3G"
        "24;9.2_3G"
        "25;9.3_3G"
        "26;9.4_3G"
        # "27;9.5_3G"
        "28;9.6_3G"
        "29;9.7_3G"
        "30;9.8_3G"
        "31;9.9_3G"
        "32;10_3G"
        "33;10_3G"
        "34;10_3G"
        "35;11_3G"
        "36;11_3G"
    )
fi

mkdir -p "outputs"
all_res_file="./outputs/$benchmark_name.res"
>$all_res_file

unix50_bash() {
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
unix50_agg() {
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
        (( ID++ ))
    done
}

unix50_bash
unix50_agg
