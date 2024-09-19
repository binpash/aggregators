#!/bin/bash

cd "$(realpath $(dirname "$0"))"
rm -rf ./outputs
rm -rf ./outputs/agg
rm -rf ./outputs-temp
rm -rf ./inputs-s-*
rm -rf ./inputs-s-par
rm -rf ./hashes
rm execution.sh
rm log.txt
