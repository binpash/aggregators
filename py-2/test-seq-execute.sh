#!/bin/bash
# A record of test (expected value) executed -- sequential command execution alreay ran
cat inputs/gb37.txt | wc > outputs/gb37-wc-seq.txt
cat inputs/gb37.txt | grep hi > outputs/gb37-grep-hi-seq.txt
cat inputs/gb37.txt | wc -l > outputs/gb37-wc--l-seq.txt
cat inputs/gb37.txt | grep -c hi > outputs/gb37-grep--c-hi-seq.txt
cat inputs/gb37II.txt | wc > outputs/gb37II-wc-seq.txt
cat inputs/gb37II.txt | grep hi > outputs/gb37II-grep-hi-seq.txt
cat inputs/gb37II.txt | wc -l > outputs/gb37II-wc--l-seq.txt
cat inputs/gb37II.txt | grep -c hi > outputs/gb37II-grep--c-hi-seq.txt
