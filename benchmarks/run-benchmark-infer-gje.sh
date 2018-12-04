#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script runs units in infer mode on all of the projects from a corpus"
    echo "Give the yml file name by itself without the file extension"
    echo "usage: $0 <some-corpus>"
    echo "eg: $0 projects"
    exit 1
fi

WORKING_DIR=$(cd $(dirname "$0") && pwd)
UI=$WORKING_DIR/..

PROJECTNAME=$1
CORPUSFILE=$WORKING_DIR/$PROJECTNAME.yml

./clean-up-projects.sh $WORKING_DIR/$PROJECTNAME

# Build jar dependency
(cd $UI && ./gradlew jar)

time python $UI/scripts/run-units-infer-gje-on-corpus.py --corpus-file $CORPUSFILE
