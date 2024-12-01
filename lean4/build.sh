#!/bin/bash

# build all executable for lean aggregators at once
lake build sort
lake build sortn
lake build sortr
lake build sortnr
lake build sortk1n
lake build uniq
lake build uniqc
lake build concat
lake build sum
lake build headn1
lake build tailn1
