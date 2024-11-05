#!/bin/bash

# Loop through all directories in the parent directory
bash_folder="outputs/bash"
folder="outputs/agg"
mkdir diff_res

echo "Generating diff for folder: $folder and $bash_folder"

# Loop through all .out files in the current directory
for file_agg in "$folder"/*.out; do
    # Extract the filename without the directory path and extension
    filename=$(basename "$file_agg" .out)

    # Compare the hash with the hash in the hashes directory
    diff $folder/"$filename".out $bash_folder/"$filename".out >diff_res/"$filename".txt
done
