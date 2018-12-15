#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script removes all inference outputs from a corpus"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

cd $1

find . -name "inferTiming\.log" | xargs rm -f
find . -name "infer\.log" | xargs rm -f
find . -name "*\.jaif" | xargs rm -f
find . -name "*\.class" | xargs rm -f
find . -name "solutions\.txt" | xargs rm -f
find . -name "statistics\.txt" | xargs rm -f
find . -name "unsatConstraints\.txt" | xargs rm -f
find . -name "slots\.smt" | xargs rm -f
find . -name "constraints\.smt" | xargs rm -f
find . -name "z3Constraints\.smt" | xargs rm -f
find . -name "z3ConstraintsUnsatCore\.smt" | xargs rm -f
find . -name "z3ConstraintsGlob\.smt" | xargs rm -f
find . -name "gjeConstraints*\.gje" | xargs rm -f
