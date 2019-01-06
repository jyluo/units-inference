#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script runs units in infer debug mode on all of the projects from a corpus"
    echo "Give the yml file name by itself without the file extension"
    echo "usage: $0 [run-in-parallel] <some-corpus>"
    echo "eg: $0 projects"
    echo "eg: $0 true projects"
    exit 1
fi

WORKING_DIR=$(cd $(dirname "$0") && pwd)
UI=$WORKING_DIR/..

PARALLEL="true"
if [ -n "$1" ] && [ $1 = "false" ]; then
    PARALLEL="false"
    shift
elif [ -n "$1" ] && [ $1 = "true" ]; then
    shift
fi

PROJECTNAME=$1
CORPUSFILE=$WORKING_DIR/$PROJECTNAME.yml

./clean-up-projects.sh $WORKING_DIR/$PROJECTNAME

# Build jar dependency
(cd $UI && ./gradlew jar)

if [ $PARALLEL = "false" ]; then
    time python $UI/scripts/run-units-debug-on-corpus.py --corpus-file $CORPUSFILE --no-run-in-parallel
else    # default mode
    time python $UI/scripts/run-units-debug-on-corpus.py --corpus-file $CORPUSFILE --run-in-parallel
fi

echo "Note: real = clock, user = sum of processes, sys = sum of kernel"
