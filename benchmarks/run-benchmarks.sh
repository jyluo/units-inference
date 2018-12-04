#!/bin/bash

gradle jar

# python run-units-infer-on-corpus.py --corpus-file=projects.yml
time python run-units-infer-on-corpus.py --corpus-file worked-benchmarks.yml
