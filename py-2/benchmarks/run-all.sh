#!/bin/bash

VERIFY=1

# verify after running each benchmark / small or reg input
if [[ "$@" == *"--v"* ]]; then
    VERIFY=0
elif [[ "$@" == *"--small"* ]]; then
    scripts_inputs=(
        "oneliners;small"
        "unix50;reg"
        "covid-mts;small"
        "nlp;small"
    )
else
    scripts_inputs=(
        "oneliners;"
        "unix50;"
        "covid-mts;"
        "nlp;"
    )
fi

run() {
    for script_input in "${scripts_inputs[@]}"; do
        IFS=";" read -r -a parsed <<<"${script_input}" # for every item in scripts_input; 0 = script and 1 = flag
        suite=${parsed[0]}
        flag=${parsed[1]}
        echo "Running ${suite} benchmarks..."
        cd "$(realpath "$(dirname "${suite}")")" || exit
        if [[ $flag == "" ]]; then
            ./run.sh
        else
            ./run.sh "${flag}"
        fi

        # if we should verify
        if [[ $VERIFY == 0 ]]; then
            ./verify.sh --generate
        fi

        cd ..
        echo "${suite} finished"
    done
}
