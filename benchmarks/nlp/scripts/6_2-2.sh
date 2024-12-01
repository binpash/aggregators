# original script: py-2/benchmarks/nlp/scripts/6_2.sh
cat $1 | tr -c 'A-Za-z' '[\n*]' | grep -v "^\s*$" | sort -u | grep -c '^....$'  
