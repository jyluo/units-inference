#!/bin/bash

./gradlew jar

CORPUSFILE="travis-benchmarks.yml"

# Running Units Inference on travis benchmarks
if [ -n "$1" ] && [ $1 = "travis" ]; then
    time python run-units-on-corpus.py --corpus-file $CORPUSFILE --is-travis-build true
else
    time python run-units-on-corpus.py --corpus-file $CORPUSFILE
fi
