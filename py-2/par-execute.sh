#!/bin/bash
inputs-s/gb01-0.txt inputs-s/gb01-1.txt inputs-s/gb01-2.txt | xargs ./s_wc.py > outputs/gb01-par.txt
