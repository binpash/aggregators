#!/bin/bash

# set -x
# install lean
cd lean4 || exit
echo "Current working directory: $(pwd)"

wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh
rm -f install_debian.sh && source ~/.profile
lake update

# build all executable for lean aggregators at once
lake build sort
# lake build sortn
# lake build sortr
# lake build sortnr
# lake build sortk1n
# lake build uniq
# lake build uniqc
# lake build concat
# lake build sum
# lake build headn1
# lake build tailn1

timestamp=$(date +"%Y-%m-%d %H:%M:%S")
echo "[$timestamp] Lean finished building. All aggregators should be in folder."

exec bash
