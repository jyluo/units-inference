#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script runs units in infer mode on all of the projects from a corpus"
    echo "Give the yml file name by itself without the file extension"
    echo "By default this runs in non-optimizing mode"
    echo "usage: $0 [optimizing-mode] [run-in-parallel] <some-corpus>"
    echo "eg: $0 projects"
    echo "eg: $0 true true projects"
    exit 1
fi

WORKING_DIR=$(cd $(dirname "$0") && pwd)
UI=$WORKING_DIR/..

OPTIMIZING_MODE="false"
if [ -n "$1" ] && [ $1 = "true" ]; then
    OPTIMIZING_MODE="true"
    shift
elif [ -n "$1" ] && [ $1 = "false" ]; then
    shift
fi

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

if [ $OPTIMIZING_MODE = "true" ] && [ $PARALLEL = "true" ]; then
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE --optimizing-mode --run-in-parallel
elif [ $OPTIMIZING_MODE = "true" ] && [ $PARALLEL = "false" ]; then
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE --optimizing-mode --no-run-in-parallel
elif [ $OPTIMIZING_MODE = "false" ] && [ $PARALLEL = "true" ]; then
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE --no-optimizing-mode --run-in-parallel
elif [ $OPTIMIZING_MODE = "false" ] && [ $PARALLEL = "false" ]; then
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE --no-optimizing-mode --no-run-in-parallel
else    # default mode
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE --no-optimizing-mode --run-in-parallel
fi

echo "Note: real = clock, user = sum of processes, sys = sum of kernel"
