#!/bin/bash
benchmark_name=nlp
export SUITE_DIR=$(realpath $(dirname $0))
export TIMEFORMAT=%R
cd "$SUITE_DIR" || exit

if [[ "$1" == "--small" ]]; then
    echo "Using small input"
    export ENTRIES=10
    export IN="$SUITE_DIR/inputs/pg-small"
elif [[ "$1" == "--test" ]]; then
    echo "Using small input"
    export ENTRIES=1
    export IN="$SUITE_DIR/inputs/pg-test"
else
    echo "Using default input"
    export ENTRIES=120
    export IN="$SUITE_DIR/inputs/pg"
fi

names_scripts=(
    "1syllable_words;6_4"
    "2syllable_words;6_5"
    "find_anagrams;8.3_2"
    "4letter_words;6_2" # split into 2 scripts
    "4letter_words;6_2-2"
    "bigrams_appear_twice;8.2_2"
    "compare_exodus_genesis;8.3_3"
     "count_consonant_seq;7_2"
    "count_trigrams;4_3b"
    "sort_words_by_folding;3_2"
    "sort_words_by_num_of_syllables;8_1"
    "trigram_rec;6_1" # split into 2 scripts
    "trigram_rec;6_1-2"
    "uppercase_by_token;6_1_1"
    "uppercase_by_type;6_1_2"
    "verses_2om_3om_2instances;6_7-2"
    "verses_2om_3om_2instances;6_7-3"
    "vowel_sequencies_gr_1K;8.2_1"
    "verses_2om_3om_2instances;6_7"
    "bigrams;4_3"
    "count_words;1_1"
    "sort;3_1"
    "sort_words_by_rhyming;3_3"
    "merge_upper;2_1"
    "count_vowel_seq;2_2"
    "count_morphs;7_1"
    "words_no_vowels;6_3"
)

# Ensure everything is unix txt format.
for file in $IN/*; do
    dos2unix $file
done

mkdir -p "outputs"
all_res_file="./outputs/$benchmark_name.res"
>$all_res_file

agg_run=../run-agg.sh 
chmod +x $agg_run 
all_args=$@
ID=1 # track agg run
nlp() {
    mkdir -p "outputs/$1"
    mode_res_file="./outputs/$1/nlp.res"

    echo executing nlp $1 $(date) | tee -a "$mode_res_file" $all_res_file

    for name_script in "${names_scripts[@]}"; do
        IFS=";" read -r -a name_script_parsed <<<"${name_script}"
        script="${name_script_parsed[1]}"
        script_file="./scripts/$script.sh"
        chmod +x $script_file
        output_dir="./outputs/$1/$script/"
        time_file="./outputs/$1/$script.time"

        if [[ "$1" == "bash" ]]; then
            IN=${IN:-$SUITE_DIR/inputs/pg}
            OUT=${output_dir:-$1/$SUITE_DIR/outputs/1_1/}
            ENTRIES=${ENTRIES:-1000}
            mkdir -p "$OUT"
            for input in $(ls ${IN} | head -n ${ENTRIES} | xargs -I arg1 basename arg1); do
                output_file=$OUT/${input}.out
                (time bash "$script_file" "$IN/$input" >"$output_file") 2>"$time_file"
                echo "$IN/$input $script_file $(cat "$time_file")" | tee -a $all_res_file

            done
        fi

        if [[ "$1" == "agg" ]]; then
            IN=${IN:-$SUITE_DIR/inputs/pg}
            OUT=${output_dir:-$1/$SUITE_DIR/outputs/1_1/}
            ENTRIES=${ENTRIES:-1000}
            mkdir -p "$OUT"
            for input in $(ls ${IN} | head -n ${ENTRIES} | xargs -I arg1 basename arg1); do
                output_file=$OUT/${input}.out
                $agg_run $script_file "$IN/$input" $output_file $time_file $ID $benchmark_name $all_res_file "$all_args"
            done
            ((ID++))
        fi

    done
}

nlp "bash"
nlp "agg"
