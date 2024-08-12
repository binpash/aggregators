# Given a script and a input file 
#   1. Parse out the commands from the entire pipeline -- (test each commands one by one) ··
#   2. With each command, find the right aggregator to use 
#   3. Run this 

## SET UP GLOBAL VARs
SPLIT_SIZE=2    # change split size for different sizes the files should be split into 
SCRIPT=$1 
INPUT_FILE=$2
FILE_TYPE=".txt"

OUTPUT_DIR="outputs-temp/agg/"
mkdir -p "${OUTPUT_DIR%/}"

# RUN THIS FILE TO EXECUTE ENTIRE SCRIPT WHEN AGG PRESENT
EXECFILE="./execution.sh"
echo "## Run this file to execute entire script considering aggregators! " > $EXECFILE

# LOG FILE FOR DEBUGGING 
LOG_FILE="log.txt"
echo "Running aggregators for script: $SCRIPT and input file: $INPUT_FILE" >> $LOG_FILE

## AGG MAP (aggregators we have)
declare -A CMDMAP=(
    ["wc"]="s_wc.py" ## for all wc and flags 
    ["grep"]="s_grep.py" 
    ["grep -c"]="s_grep.py -c" 
    ["uniq"]="s_uniq.py" 
    ["uniq -c"]="s_uniq.py -c"
    ["head"]="s_head.py"
    ["tail"]="s_tail.py"
    ["tail -n"]="NA"
    ["sort"]="s_sort.py"
    ["sort -nr"]="s_sort.py -rn"
    ["sort -rn"]="s_sort.py -rn"
    ["sort -n"]="s_sort.py -n"
    ["sort -r"]="s_sort.py -r"
    ["sort -u"]="s_sort.py -u"
    ["sort -k 1 -n"]="NA"
    ) 

seq() {
    S_OUTPUT=$(../test-seq-driver.sh "$1" "$2" "$3" "$4" "$5")
}

par() {
    P_OUTPUT=$(../test-par-driver.sh "$1" "$2" "$3" "$4" "$5" "$6" "$7" "$8")
}

parse_simple() {
    CMDLIST=()
    while IFS= read -r line; do
        # Skip comments and empty lines
        if [[ "$line" == \#* ]] || [[ -z "$line" ]]; then
            continue
        fi
        
        # Parse out simple one-line commands separated by "|"
        # Leave out the first 'cat $1' for reading in input file
        IFS='|' read -ra CMDLIST <<< "$line"        
        if [[ "${CMDLIST[0]}" == cat* ]]; then
            CMDLIST=("${CMDLIST[@]:1}")
        fi
    done < "$SCRIPT"
}

mkdir_get_split() {
    local FILE=$1
    WITHOUTTXT=$(basename "${FILE}" .txt)
    SPLIT_DIR="inputs-s/${WITHOUTTXT}/"
    mkdir -p "${SPLIT_DIR%/}"  
    if [ $(wc -l < "$FILE" ) -le 0 ]; then 
        touch "${SPLIT_DIR}${WITHOUTTXT}"-00.txt 
    else 
        split -dl $(($(wc -l < "$FILE") / SPLIT_SIZE)) -a 2 --additional-suffix=${FILE_TYPE} "$FILE" "${SPLIT_DIR}${WITHOUTTXT}"-
    fi 
    split_files=("${SPLIT_DIR}${WITHOUTTXT}-"*)    
    echo "${split_files[@]}"
}

# function to find the right agg. given a CMD
find_agg() {
    local FULL=$(echo "$1" | xargs)
    
    # Parse CMD out from Flags
    CMD="$(echo "${FULL}" | cut -d ' ' -f1)"
    FLAG="$(echo "${FULL}" | cut -d ' ' -f2)"

    # see if we use flags
    if [ "${FLAG:0:1}" = "-" ]; then
        PARSE="$CMD $FLAG"
        
        # CMD has a flag specific agg
        #   EX: grep -c => grep_c
        RESULT="${CMDMAP["$PARSE"]}"
       
        # # if the agg doesn't have a flag version, return agg without flags
        # #   wc -l => wc & wc -lm => wc (share same agg)
        if [ -z "${RESULT}" ]; then
            RESULT=${CMDMAP[${CMD}]}
        fi
    else
        # Don't use flags
        PARSE=$CMD
        if [[  -n "$CMD" ]]; then 
            RESULT=${CMDMAP[${CMD}]}
        fi 
    fi
    echo "${RESULT}"
}

run() {
    parse_simple # get CMDLIST, an array holding all single commands
    local CURR_CMD_COUNT=0
    for CMD in "${CMDLIST[@]}"; do

        if [[ $CURR_CMD_COUNT == 0 ]]; then 
            CURR_INPUT=$INPUT_FILE
        fi
        AGG="$(find_agg "${CMD}")"  # See if agg exist
        if [[ -z "$AGG" || "$AGG" == "NA" ]]; then 
        ## agg not found, pass entire input through cmd as normal 
            echo "NOT IMPLEMENTED: $CMD" >> $LOG_FILE 
            # get sequential execution line
            seq "${CURR_INPUT}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${EXECFILE}"
            # execute sequentially 
            eval "$S_OUTPUT"
            # parse out the output file to use as next input
            CURR_INPUT=$(echo "$S_OUTPUT" | awk -F '> ' '{print $2}')
        else
        ## has agg for cmd + flag
            echo "IMPLEMENTED: $CMD" >> $LOG_FILE 
            # split input according to split size
            local SPLIT_FILELIST=$(mkdir_get_split "$CURR_INPUT")
            # run each split file through par driver; which runs split files under cmd and return cmd line to run correct agg on those files
            par "${CURR_INPUT}" "${OUTPUT_DIR}" "${FILE_TYPE}" "${CMD}" "${AGG}" "${EXECFILE}" "${SPLIT_FILELIST[@]}" "inputs-s"
            # run agg script with files ran with cmd 
            eval "$P_OUTPUT"
            # parse out the output file to use as next input
            CURR_INPUT=$(echo "$P_OUTPUT" | awk -F '> ' '{print $2}')
        fi
        ((CURR_CMD_COUNT++))
    done

    # print final result to output file
    cat $CURR_INPUT 
}

run