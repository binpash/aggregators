#!/bin/bash
# A record of test (expected value) executed -- sequential command execution alreay ran
cat inputs/hi.txt | grep is > outputs/hi-grep-is-seq.txt
cat inputs/hi.txt | wc -cl > outputs/hi-wc--cl-seq.txt
cat inputs/hi.txt | grep -c hi > outputs/hi-grep--c-hi-seq.txt
cat inputs/hi.txt | wc > outputs/hi-wc-seq.txt
cat inputs/hi.txt | grep Twentieth > outputs/hi-grep-Twentieth-seq.txt
cat inputs/hi.txt | wc -w -m > outputs/hi-wc--w--m-seq.txt
cat inputs/gb37.txt | grep is > outputs/gb37-grep-is-seq.txt
cat inputs/gb37.txt | wc -cl > outputs/gb37-wc--cl-seq.txt
cat inputs/gb37.txt | grep -c hi > outputs/gb37-grep--c-hi-seq.txt
cat inputs/gb37.txt | wc > outputs/gb37-wc-seq.txt
cat inputs/gb37.txt | grep Twentieth > outputs/gb37-grep-Twentieth-seq.txt
cat inputs/gb37.txt | wc -w -m > outputs/gb37-wc--w--m-seq.txt
cat inputs/gb37II.txt | grep is > outputs/gb37II-grep-is-seq.txt
cat inputs/gb37II.txt | wc -cl > outputs/gb37II-wc--cl-seq.txt
cat inputs/gb37II.txt | grep -c hi > outputs/gb37II-grep--c-hi-seq.txt
cat inputs/gb37II.txt | wc > outputs/gb37II-wc-seq.txt
cat inputs/gb37II.txt | grep Twentieth > outputs/gb37II-grep-Twentieth-seq.txt
cat inputs/gb37II.txt | wc -w -m > outputs/gb37II-wc--w--m-seq.txt
cat inputs/gb70.txt | grep is > outputs/gb70-grep-is-seq.txt
cat inputs/gb70.txt | wc -cl > outputs/gb70-wc--cl-seq.txt
cat inputs/gb70.txt | grep -c hi > outputs/gb70-grep--c-hi-seq.txt
cat inputs/gb70.txt | wc > outputs/gb70-wc-seq.txt
cat inputs/gb70.txt | grep Twentieth > outputs/gb70-grep-Twentieth-seq.txt
cat inputs/gb70.txt | wc -w -m > outputs/gb70-wc--w--m-seq.txt
cat inputs/gb71.txt | grep is > outputs/gb71-grep-is-seq.txt
cat inputs/gb71.txt | wc -cl > outputs/gb71-wc--cl-seq.txt
cat inputs/gb71.txt | grep -c hi > outputs/gb71-grep--c-hi-seq.txt
cat inputs/gb71.txt | wc > outputs/gb71-wc-seq.txt
cat inputs/gb71.txt | grep Twentieth > outputs/gb71-grep-Twentieth-seq.txt
cat inputs/gb71.txt | wc -w -m > outputs/gb71-wc--w--m-seq.txt
cat inputs/gb72.txt | grep is > outputs/gb72-grep-is-seq.txt
cat inputs/gb72.txt | wc -cl > outputs/gb72-wc--cl-seq.txt
cat inputs/gb72.txt | grep -c hi > outputs/gb72-grep--c-hi-seq.txt
cat inputs/gb72.txt | wc > outputs/gb72-wc-seq.txt
cat inputs/gb72.txt | grep Twentieth > outputs/gb72-grep-Twentieth-seq.txt
cat inputs/gb72.txt | wc -w -m > outputs/gb72-wc--w--m-seq.txt
