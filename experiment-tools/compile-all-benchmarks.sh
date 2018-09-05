#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script compiles units inference and all of the projects from a corpus without running any benchmarking"
    echo "Give the yml file name by itself, as located in units-inference root directory"
    echo "usage: $0 <some-corpus>.yml"
    echo "eg: ./compile-all-benchmarks.sh projects.yml"
    exit 1
fi

# ./compile-all-benchmarks.sh projects.yml

# set -e

(cd ../ && gradle jar)

# python run-units-on-corpus.py --corpus-file=projects.yml
time python ./../run-corpus-no-tool.py --corpus-file $1
