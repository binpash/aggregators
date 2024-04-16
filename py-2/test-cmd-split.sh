#!/bin/bash

mkdir outputs
mkdir inputs

# make cmd to agg. map to get which cmd should be used
declare -A CMDMAP
CMDMAP["wc"]="s_wc.py"
CMDMAP["grep"]="s_grep.py"
CMDMAP["grep -c"]="s_grep_c.py"

# Global variables
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"
P='./par-execute.sh'
CMDLIST=(wc)

# Build par execute file
echo '#!/bin/bash' >$P
chmod +x $P

FULLFILE="gb01"
SPLIT_SIZE=2
wget --no-check-certificate 'https://atlas.cs.brown.edu/data/gutenberg/0/1/old/1.txt' -O inputs/${FULLFILE}${FILE_TYPE}

# SAME FOR ALL FILES
mkdir inputs-s
split -dl $(($(wc -l < inputs/${FULLFILE}.txt) / SPLIT_SIZE)) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FULLFILE}.txt inputs-s/${FULLFILE}-
# apply command to all split files
for CMD in "${CMDLIST[@]}"; do
    cd inputs-s
    for FILE in *; do
	echo ${FILE} 
	$CMD ${FILE} | sponge ${FILE} 
    done 
    cd .. 
    chmod +x ./s_"$CMD".py
    filelist=$(ls -p inputs-s/*)
    echo $filelist 
    echo ""$filelist" | xargs ./s_$CMD.py > ${OUTPUT_DIR}${FULLFILE}-par.txt" >> $P
    # echo "./s_"$CMD".py $filelist > ${OUTPUT_DIR}"${FULLFILE}"-par.txt" > $P
done

# Old piping method, doesn't seem to work but seems more efficient
# IFS=''
# split -dl $(($(wc -l <inputs/${FILE}.txt) / SPLIT_SIZE)) -a 1 --additional-suffix=${FILE_TYPE} ${INPUT_DIR}${FILE}.txt |
#     while read -r -d split_file; do
#         wc <"$split_file" >"${OUTPUT_DIR}3-${FILE}${FILE_TYPE}"
#     done
