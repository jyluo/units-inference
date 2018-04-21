#!/bin/bash

#./clean-up-projects.sh projects

gradle jar

# python run-units-on-corpus.py --corpus-file=projects.yml
time python run-units-typecheck-on-corpus.py --corpus-file projects.yml