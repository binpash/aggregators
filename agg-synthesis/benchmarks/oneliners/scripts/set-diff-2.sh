## modified original script above to take out main pipeline relevant to agg. 
# second pipeline 
# original: benchmarks/oneliners/scripts/set-diff.sh

cat $1 | cut -d ' ' -f 1 | sort 
