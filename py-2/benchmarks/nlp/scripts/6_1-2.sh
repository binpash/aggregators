# modified for agg. 
# original script: py-2/benchmarks/nlp/scripts/6_1.sh
cat $1 | grep 'And he said' | sort -nr | sed 5q 
