#!/bin/bash

# builds & test units-inference, runs it on the corpus, and grabs the results

# Split $TRAVIS_REPO_SLUG into the owner and repository parts
OIFS=$IFS
IFS='/'
read -r -a slugarray <<< "$TRAVIS_REPO_SLUG"
SLUGOWNER=${slugarray[0]}
SLUGREPO=${slugarray[1]}
IFS=$OIFS

export REPO_SITE=$SLUGOWNER

# Build dependencies
. ./dependency-setup.sh

# Failed the whole script if any command failed
set -e

# Running Units Inference test suite
export JSR308=$(cd $(dirname "$0")/.. && pwd)
export PATH=$JSR308/z3/bin:$PATH
./gradlew test

# Running Units Inference on working benchmarks
. ./run-travis-benchmarks.sh travis

# Print summary stats
. ./experiment-tools/gen-inference-summary.sh travis-benchmarks
