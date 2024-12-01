#!/bin/bash

# Given a benchmark script and an input file
#   1. Parse out each command from the entire pipeline -- (test each commands one by one) ··
#   2. With each command, check if agg exist to combine parallel result
#   3. If agg exists, run in parallel
#   4. If agg don't exists or err with agg, run sequentially
#   5. Use aggregated output as input to next cmd run

## SET UP GLOBAL VARs
SPLIT_SIZE=2 # change split size for different sizes the files should be split into
SCRIPT=$1
INPUT_FILE=$2
FILE_TYPE="" # default text file
SPLIT_TOP="inputs-s-"$3
OUTPUT_DIR="outputs-temp/agg/"
DEBUG_LOG=$4
EXECFILE=$5
cmd_instance_counter=$6
mkdir -p "${OUTPUT_DIR%/}"

# This script is to trace each command instance
# We can see if each command is ran in parallel or in sequential
# This script is executable to re-run the entire aggregator application pipeline
printf "#!/bin/bash\n \n" >$EXECFILE
printf "## EXEC: this script records each evaluation (seq or par) to reach the final output \n" >>$EXECFILE

# This log file is to record down a general
printf "LOG: Running aggregators for script: $SCRIPT and input file: $INPUT_FILE\n" >"$DEBUG_LOG"

seq() {
    S_OUTPUT=$(../test-seq-driver.sh "$1" "$2" "$3" "$4" "$5")
}

par() {
    P_OUTPUT=$(../test-par-driver.sh "$1" "$2" "$3" "$4" "$5" "$6" "$7" "$8")
}

parse_simple() {
    echo "LOG: " "Parsing command pipeline from $SCRIPT" >"$DEBUG_LOG"
    while IFS= read -r line; do
        # Skip comments and empty lines
        if [[ "$line" == \#* ]] || [[ -z "$line" ]]; then
            continue
        fi

        # Parse out simple one-line commands separated by "|"
        # Leave out the first 'cat $1' for reading in input file
        IFS='|' read -ra CMDLIST <<<"$line"
        if [[ "${CMDLIST[0]}" == cat* ]]; then
            CMDLIST=("${CMDLIST[@]:1}")
        fi
    done <"$SCRIPT"

}

mkdir_get_split() {
    echo "$LOG_PREFIX" "Getting partials: trying to split input into $SPLIT_SIZE even partials" >>"$DEBUG_LOG"
    local FILE=$1
    WITHOUTTXT=$(basename "${FILE}" .txt)
    SPLIT_DIR="${SPLIT_TOP}/${WITHOUTTXT}/"
    mkdir -p "${SPLIT_DIR%/}"
    # split -dl $(($(wc -l <"$FILE") / SPLIT_SIZE)) -a 2 --additional-suffix=${FILE_TYPE} "$FILE" "${SPLIT_DIR}${WITHOUTTXT}"-
    ## BSD
    split -dl $(($(wc -l <"$FILE") / SPLIT_SIZE)) -a 2 "$FILE" "${SPLIT_DIR}${WITHOUTTXT}"-
    split_files=("${SPLIT_DIR}${WITHOUTTXT}-"*)
    echo "${split_files[@]}"
    echo "$LOG_PREFIX" "Getting partials: got ${#split_files[@]} partials in return of splitting" >>"$DEBUG_LOG"
}

# function to find the right agg. given a CMD
find_agg() {
    local FULL=$(echo "$1" | xargs)

    # Parse CMD out from Flags
    CMD="$(echo "${FULL}" | cut -d ' ' -f1)"
    FLAG="$(echo "${FULL}" | cut -d ' ' -f2-)"

    # see if we use flags, build agg file path
    AGG_FILE_NO_FLAG="s_$CMD.py"
    if [ "${FLAG:0:1}" = "-" ]; then
        AGG_FILE="s_$CMD.py $FLAG" # CHANGE AGG
    else
        AGG_FILE=$AGG_FILE_NO_FLAG
    fi

    ## COMMENT OUT FOR lean
    # AGG_FILE_NO_FLAG="aggregators"

    #AGG_FILE=$AGG_FILE_NO_FLAG

    # check if the agg exist
    if [ -f "../../${AGG_FILE_NO_FLAG}" ]; then
        echo "${AGG_FILE}"
    else
        echo ""
    fi
}

run() {
    parse_simple # get CMDLIST, an array holding all single commands
    cmd_count_with_cat=$((${#CMDLIST[@]} + 1))
    echo $cmd_count_with_cat >>$cmd_instance_counter
    echo "LOG: " "Parsing command pipeline finished; we have ${#CMDLIST[@]} command instances" >>"$DEBUG_LOG"

    local CURR_CMD_COUNT=0
    for CMD in "${CMDLIST[@]}"; do
        LOG_PREFIX="LOG: $CMD | "

        if [[ $CURR_CMD_COUNT == 0 ]]; then
            CURR_INPUT=$INPUT_FILE
        fi
        AGG="$(find_agg "${CMD}")" # See if agg exist
        if [[ -z "$AGG" || "$AGG" == "NA" ]]; then
            ## agg not found, pass entire input through cmd as normal
            echo "$LOG_PREFIX" "Running command sequentially: aggregator not found " >>"$DEBUG_LOG"
            echo "$LOG_PREFIX" "Aggregator Status: not implemented " >>"$DEBUG_LOG"
            # get sequential execution line
            seq "${CURR_INPUT}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${EXECFILE}"
            # execute sequentially
            eval "$S_OUTPUT"
            # parse out the output file to use as next input
            CURR_INPUT=$(echo "$S_OUTPUT" | awk -F '> ' '{print $2}')
        else
            ## agg for cmd + flag found
            echo "$LOG_PREFIX" "Running aggregators with parallel partial " >>"$DEBUG_LOG"
            echo "$LOG_PREFIX" "Aggregator Status: implemented " >>"$DEBUG_LOG"
            # split input according to split size; don't split if the file is empty
            if ! grep -q . "$CURR_INPUT"; then
                echo "$LOG_PREFIX" "Running command sequentially: input file is empty " >>"$DEBUG_LOG"
                echo "$LOG_PREFIX" "Aggregator Status: implemented " >>"$DEBUG_LOG"
                seq "${CURR_INPUT}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${EXECFILE}"
                eval "$S_OUTPUT"
                CURR_INPUT=$(echo "$S_OUTPUT" | awk -F '> ' '{print $2}')
            else
                local SPLIT_FILELIST=$(mkdir_get_split "$CURR_INPUT")
                # run each split file through par driver; which runs split files under cmd and return cmd line to run correct agg on those files
                par "${CURR_INPUT}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${AGG}" "${EXECFILE}" "${SPLIT_FILELIST[@]}" "${SPLIT_TOP}"
                # run agg script with files ran with cmd
                eval "$P_OUTPUT"
                if [ $? -eq 1 ]; then
                    echo "$LOG_PREFIX" "ERROR: Aggregator failed (Cannot read in input file correctly)" >&2 >>"$DEBUG_LOG"
                    echo "$LOG_PREFIX" "Running sequentially: aggregator error " >>"$DEBUG_LOG"
                    echo "$LOG_PREFIX" "Aggregator Status: implemented " >>"$DEBUG_LOG"
                    seq "${CURR_INPUT}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${EXECFILE}"
                    eval "$S_OUTPUT"
                    CURR_INPUT=$(echo "$S_OUTPUT" | awk -F '> ' '{print $2}')
                else
                    # parse out the output file to use as next input
                    CURR_INPUT=$(echo "$P_OUTPUT" | awk -F '> ' '{print $2}')
                    echo "$LOG_PREFIX" "Aggregator applied with no error reported " >>"$DEBUG_LOG"
                fi
            fi
        fi
        ((CURR_CMD_COUNT++))
    done

    # print final result to output file
    cat "$CURR_INPUT"
}

run
