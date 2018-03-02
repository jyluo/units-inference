#!/bin/bash

echo " START TIME : "
date
echo ""

# python run-units-on-corpus.py --corpus-file=projects.yml
python run-units-on-corpus.py --corpus-file worked-benchmarks.yml

echo " END TIME : "
date
echo ""
