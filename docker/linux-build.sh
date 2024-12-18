#!/bin/bash

# set -x
timestamp=$(date +"%Y-%m-%d %H:%M:%S")
(
    # install lean
    cd lean4
    echo "[$timestamp] Installing lean dependencies."
    echo "[$timestamp] Current working directory: $(pwd)"

    wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh
    rm -f install_debian.sh && source ~/.profile
    lake update

    echo "[$timestamp] Building lean executables."

    # build all executable for lean aggregators at once
    chmod +x ./build.sh
    ./build.sh

    echo "[$timestamp] Lean finished building. All aggregators should be in folder."
)

(
    echo "[$timestamp] Setting up simple infra"
    cd benchmarks/simple_infra/exec_scripts || exit
    chmod +x ./test-par-driver.sh
    chmod +x ./test-seq-driver.sh
)

echo "[$timestamp] Finish setting up all container dependencies."
exec bash
