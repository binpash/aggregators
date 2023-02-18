#!/usr/bin/env bash

set -x e

export PASH_AGGS_TOP=${PASH_AGGS_TOP:-$(git rev-parse --show-toplevel --show-superproject-working-tree)}

echo "Running aggregator tests..."
cd "$PASH_AGGS_TOP/tests/agg/"
./run.sh

echo "Running aggregator tests..."
cd "$PASH_AGGS_TOP/cpp/tests"
./test.sh

