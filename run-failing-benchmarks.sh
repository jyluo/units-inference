#!/bin/bash

find . -name "infer\.log" | xargs rm

gradle jar

# python run-units-on-corpus.py --corpus-file=projects.yml
time python run-units-on-corpus.py --corpus-file failing-benchmarks.yml