if [[ -z "$PASH_AGG_TOP" ]]; then
    export PASH_AGG_TOP=${PASH_AGG_TOP:-$(git rev-parse --show-toplevel --show-superproject-working-tree)}
fi

export IN1=$PASH_AGG_TOP/cpp/tests/input/1M.txt
export IN2=$PASH_AGG_TOP/cpp/tests/input/words

"$PASH_AGG_TOP/cpp/tests/input/setup.sh"

if [[ $(uname -s) == 'Linux' ]]; then
    ./test-linux.sh
elif [[ $(uname -s) == 'FreeBSD' ]]; then
    ./test-bsd.sh
fi
