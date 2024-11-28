cat $1 | awk '($9 ~ /404/)' ${INPUT} | awk -F\" '($2 ~ "^GET .*\.php")' | awk '{print $7}' | sort | uniq -c | sort -r | head -n 20
