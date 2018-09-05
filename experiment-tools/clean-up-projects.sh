#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script removes all inference outputs from a corpus"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

cd $1

find . -name "infer\.log" | xargs rm
find . -name "*\.jaif" | xargs rm
find . -name "*\.class" | xargs rm
find . -name "statistic\.txt" | xargs rm
find . -name "solutions\.txt" | xargs rm
find . -name "z3Constraints\.smt" | xargs rm
find . -name "z3ConstraintStats\.smt" | xargs rm
