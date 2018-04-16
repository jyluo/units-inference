#!/bin/bash

gradle jar

# python run-units-on-corpus.py --corpus-file=projects.yml
time python run-corpus-no-tool.py --corpus-file projects.yml