#!/bin/bash

RUN=0
VERIFY=1
CLEAN_UP=1

# verify after running each benchmark / small or reg input
if [[ "$@" == *"--v"* ]]; then
    VERIFY=0
fi

# verify only
if [[ "$@" == *"--v_only"* ]]; then
    VERIFY=0
    RUN=1
fi

# cleanup after running each benchmark / small or reg input
if [[ "$@" == *"--c"* ]]; then
    CLEAN_UP=0
fi

# clean up only
if [[ "$@" == *"--c_only"* ]]; then
    CLEAN_UP=0
    RUN=1
fi

# EDIT: edit here for benchmark suites to run
if [[ "$@" == *"--small"* ]]; then
    scripts_inputs=(
        "oneliners;small"
        # "unix50;reg"
        # "covid-mts;small"
        # "nlp;small"
    )
elif [[ "$@" == *"--single"* ]]; then
    scripts_inputs=(
        "oneliners;single"
        # "unix50;reg"
        # "covid-mts;small"
        # "nlp;small"
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
        cd "$(realpath "$(dirname "${suite}")")/${suite}" || exit

        # if we should run scripts
        if [[ $RUN == 0 ]]; then
            echo "Running ${suite} benchmarks..."
            if [[ $flag == "" ]]; then
                ./run.sh
            else
                ./run.sh "--${flag}"
            fi
        fi

        # if we should verify
        if [[ $VERIFY == 0 ]]; then
            ./verify.sh --generate
        fi

        # if we should clean-up
        if [[ $CLEAN_UP == 0 ]]; then
            ./cleanup.sh
        fi

        cd ..
        echo "${suite} finished"
    done
}

run
