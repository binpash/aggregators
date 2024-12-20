#!/bin/bash 

benchmarks=(
        "oneliners"
        "unix50"
        "covid-mts"
        # "nlp"
    )

args=$@

run_all() {
    for benchmark in "${benchmarks[@]}"; do 
        chmod +x ./$benchmark/run.sh
        ./$benchmark/run.sh $args
    done 

    echo "--------------- DONE ---------------"
    for benchmark in "${benchmarks[@]}"; do 
        echo "$benchmark debug log: ./$benchmark/infra_debug.log"
        echo "$benchmark CSV: ./$benchmark/infra_metrics.csv" 
    done 
    
    echo To clean up, use: ./run-all.sh --clean
}

inputs() {
    for benchmark in "${benchmarks[@]}"; do 
        chmod +x ./$benchmark/run.sh
        ./$benchmark/cleanup.sh
    done 
}


clean_all() {
    for benchmark in "${benchmarks[@]}"; do 
        chmod +x ./$benchmark/run.sh
        ./$benchmark/cleanup.sh
    done 
}


inputs() {
    for benchmark in "${benchmarks[@]}"; do 
        chmod +x ./$benchmark/inputs.sh
        ./$benchmark/inputs.sh
    done 
}


if [[ "$@" == *"--clean"* ]]; then
    clean_all
elif [[ "$@" == *"--inputs"* ]]; then
    inputs
else
    run_all
fi
    