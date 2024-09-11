#!/bin/bash

REPO_TOP=$(git rev-parse --show-toplevel)
results_dir="${REPO_TOP}/covid-mts/results"

echo "Cleaning up outputs..."
rm -rf $results_dir