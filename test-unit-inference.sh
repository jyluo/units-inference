#!/bin/bash

# Failed the whole script if any command failed
set -e

# Running Units Inference test suite
gradle test

# Running Units Inference on working benchmarks
python run-units-on-corpus.py --corpus-file worked-benchmarks.yml
