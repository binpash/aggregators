#!/bin/bash
# Hours each bus is active each day

# Records are day, hour, line, bus
cat $1 | awk -F\" '($2 ~ "/wp-admin/install.php"){print $1}' ${INPUT} | awk '{print $1}' | sort | uniq -c | sort -r
