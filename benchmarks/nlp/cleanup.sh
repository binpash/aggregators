#!/bin/bash

cd "$(realpath $(dirname "$0"))"

rm -rf ./outputs
rm -rf ./outputs-temp
rm -rf ./inputs-s-*
rm -rf ./inputs-s-par
rm -rf ./hashes 
rm -rf "./agg-steps"
rm infra_debug.log
rm infra_metrics.csv