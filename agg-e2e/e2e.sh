#!/bin/bash

# We begin our e2e execution of the benchmark infra. with,
#   - a command instance, in the form of a .sh script
#   - the original input
#   - annotations JSON
SCRIPT=$1
INPUT_FILE=$2
ANNOTATIONS=$3

# Tracking purposes for debugging
DEBUG_LOG=$4
LOG_PREFIX="E2E LOG:"

# Synthesis:
# Here, provided the annotations JSON, we will run the synthesis script.
# TODO (@Roberto): change synthesizer script to take in annotations.json as an argument
# TODO (@Roberto): also seems like running the script produces a directory.
#   Is it possible to direct all needed components to one file that
#       sits in the root of the agg-e2e directory?
export SYN_DIR=$(realpath $(dirname "synthesis"))
SYN_SCRIPT="synthesizer.py"
# # TODO (@Roberto): Whatever you call the file you, set it to SYN_RECIPE
SYN_RECIPE="" # TODO (@Roberto): Whatever you call the file you
printf "%s\n" "$LOG_PREFIX Generating synthesis file for verification step"
# TODO (@Megan): Add timer here to time synthesis
python3 "$SYN_DIR"/"$SYN_SCRIPT" "$ANNOTATIONS" >$SYN_RECIPE

# Verification:
# Here, we take the output of the synthesis step to verify.
# We will retrun with a compiled binary.
# TODO (@Chloe): can we move the lean4 folder to inside agg-synthesis?
# TODO (@Chloe): let's ensure that the binary produced is named "cmd-flag" and redirected to COMPILED_DIR
LEAN_START=""
COMPILED_DIR="Aggregators"
mkdir -p $COMPILED_DIR
$LEAN_START $SYN_RECIPE

# Benchmark Infrastructure / Testing:
# Here, we need the script, original input, Executable aggregator binary.
# We should run verify to determine if the bash produces exact answer.
printf "%s\n" "$LOG_PREFIX Running script $SCRIPT and input $INPUT with benchmark infrastructure" | tee -a "$DEBUG_LOG"
./run.sh "$SCRIPT" "$INPUT_FILE" "$DEBUG_LOG"

printf "%s\n" "$LOG_PREFIX Verifying aggregator results to bash" | tee -a "$DEBUG_LOG"
./verify.sh --generate

printf "%s\n" "$LOG_PREFIX Cleaning up benchmark directory intermediate files" | tee -a "$DEBUG_LOG"
./cleanup.sh
