#!/bin/bash
cat inputs-s/gb-0.txt | wc > outputs/gb-0-wc.txt
cat inputs-s/gb-1.txt | wc > outputs/gb-1-wc.txt
cat inputs-s/gb-2.txt | wc > outputs/gb-2-wc.txt
cat inputs-s/gb-0.txt | grep and > outputs/gb-0-grep-and.txt
cat inputs-s/gb-1.txt | grep and > outputs/gb-1-grep-and.txt
cat inputs-s/gb-2.txt | grep and > outputs/gb-2-grep-and.txt
cat inputs-s/gb-0.txt | grep project > outputs/gb-0-grep-project.txt
cat inputs-s/gb-1.txt | grep project > outputs/gb-1-grep-project.txt
cat inputs-s/gb-2.txt | grep project > outputs/gb-2-grep-project.txt
cat inputs-s/gb-0.txt | grep -c Project > outputs/gb-0-grep--c-Project.txt
cat inputs-s/gb-1.txt | grep -c Project > outputs/gb-1-grep--c-Project.txt
cat inputs-s/gb-2.txt | grep -c Project > outputs/gb-2-grep--c-Project.txt
cat inputs-s/gb-0.txt | wc -lm > outputs/gb-0-wc--lm.txt
cat inputs-s/gb-1.txt | wc -lm > outputs/gb-1-wc--lm.txt
cat inputs-s/gb-2.txt | wc -lm > outputs/gb-2-wc--lm.txt
cat inputs-s/gb-0.txt | wc -c > outputs/gb-0-wc--c.txt
cat inputs-s/gb-1.txt | wc -c > outputs/gb-1-wc--c.txt
cat inputs-s/gb-2.txt | wc -c > outputs/gb-2-wc--c.txt
