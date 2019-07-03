#!/bin/bash
ROOT=$(realpath .)
OUTPUT=$ROOT/output

function compile {
    echo "compiling $1 ..."
    mkdir -p $OUTPUT
    rm -f $OUTPUT/$1.ll $OUTPUT/$1.s $OUTPUT/$1
    dotnet run --no-build -p $ROOT/driver -- $ROOT/tests/$1.pk $OUTPUT/$1.ll
    llc -relocation-model=pic $OUTPUT/$1.ll
    cc $OUTPUT/$1.s -o $OUTPUT/$1
}

function compare {
    compile $1
    $OUTPUT/$1 > $OUTPUT/$1.out
    diff $OUTPUT/$1.out $ROOT/tests/$1.expect
}

if [ -z "$1" ]; then
    for test_file in $ROOT/tests/*.pk; do
        TEST=$(basename ${test_file%.*})
        if [ -f $ROOT/tests/$TEST.expect ]; then
            compare $TEST &
            sleep .3
        fi
    done
else
    compare $1
fi

wait
