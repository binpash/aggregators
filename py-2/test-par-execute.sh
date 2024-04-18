#!/bin/bash
# Already executed -- records down what was exectued
./s_grep_c.py inputs-s-par/gb37II-0-grep--c-hi.txt inputs-s-par/gb37II-1-grep--c-hi.txt  > outputs/gb37II-grep--c-hi-par.txt
./s_wc.py inputs-s-par/gb37II-0-wc.txt inputs-s-par/gb37II-1-wc.txt  > outputs/gb37II-wc-par.txt
./s_grep.py inputs-s-par/gb37II-0-grep-and.txt inputs-s-par/gb37II-1-grep-and.txt  > outputs/gb37II-grep-and-par.txt
./s_wc.py inputs-s-par/gb37II-0-wc--lm.txt inputs-s-par/gb37II-1-wc--lm.txt  > outputs/gb37II-wc--lm-par.txt
