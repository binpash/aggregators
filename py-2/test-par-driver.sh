#!/bin/bash

mkdir outputs

# Global variables
INPUT_DIR="inputs/"
OUTPUT_DIR="outputs/"
FILE_TYPE=".txt"
P='./par-execute.sh'
CMDLIST=("wc" "grep and" "grep project" "grep -c Project" "wc -lm" "wc -c")

# Build par files
echo '#!/bin/bash' >$P
chmod +x $P
