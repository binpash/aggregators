#!/bin/bash

cd "$(realpath $(dirname "$0"))"
ls
rm -rf ./outputs
rm -rf ./outputs-temp
rm -rf ./inputs-s-par
rm -rf ./inputs-s-*
rm -rf ./hashes
rm execution.sh 
rm log.txt
