#!/bin/bash

WORKING_DIR=$(cd $(dirname "$0") && pwd)
UI=$WORKING_DIR/..

PROJECTNAME=travis-benchmarks
CORPUSFILE=$WORKING_DIR/$PROJECTNAME.yml

# Build jar dependency
(cd $UI && ./gradlew jar)

# Running Units Inference on travis benchmarks
if [ -n "$1" ] && [ $1 = "travis" ]; then
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE --is-travis-build true
else
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE
fi
