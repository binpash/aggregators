#!/bin/bash
# Already executed -- records down what was exectued
cat inputs/gb37II.txt | grep -c hi > outputs/gb37II-grep--c-hi-seq.txt
cat inputs/gb37II.txt | wc > outputs/gb37II-wc-seq.txt
cat inputs/gb37II.txt | grep and > outputs/gb37II-grep-and-seq.txt
cat inputs/gb37II.txt | wc -lm > outputs/gb37II-wc--lm-seq.txt
