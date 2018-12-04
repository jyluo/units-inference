#!/bin/bash

find . -name "infer\.log" | xargs rm

gradle jar

# python run-units-infer-on-corpus.py --corpus-file=projects.yml
time python run-units-infer-on-corpus.py --corpus-file failing-benchmarks.yml
