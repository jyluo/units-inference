#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script runs units in infer mode on all of the projects from a corpus"
    echo "Give the yml file name by itself without the file extension"
    echo "By default this runs in non-optimizing mode"
    echo "usage: $0 [optimizing-mode] <some-corpus>"
    echo "eg: $0 projects"
    echo "eg: $0 true projects"
    exit 1
fi

WORKING_DIR=$(cd $(dirname "$0") && pwd)
UI=$WORKING_DIR/..

OPTIMIZING_MODE="false"
if [ -n "$1" ] && [ $1 = "true" ]; then
    OPTIMIZING_MODE="true"
    shift
fi

PROJECTNAME=$1
CORPUSFILE=$WORKING_DIR/$PROJECTNAME.yml

./clean-up-projects.sh $WORKING_DIR/$PROJECTNAME

# Build jar dependency
(cd $UI && ./gradlew jar)

if [ $OPTIMIZING_MODE = "true" ]; then
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE --optimizing-mode true
else
    time python $UI/scripts/run-units-infer-on-corpus.py --corpus-file $CORPUSFILE
fi

echo "Real = clock, user = sum of processes, sys = sum of kernel"
