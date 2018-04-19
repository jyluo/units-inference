#!/bin/bash

find . -name "infer\.log" | xargs rm
find . -name "statistic\.txt" | xargs rm
find . -name "solutions\.txt" | xargs rm

gradle jar

# python run-units-on-corpus.py --corpus-file=projects.yml
time python run-units-on-corpus.py --corpus-file projects.yml