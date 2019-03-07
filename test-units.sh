#!/bin/bash

# Failed the whole script if any command failed
set -e

WORKING_DIR=$(pwd)

if [ -z "${JSR308}" ] ; then
    export JSR308=$(cd $(dirname "$0")/.. && pwd)
fi
export PATH=$JSR308/z3/bin:$PATH

# Pull DLJC if it doesn't exist
# This is for downstream travis test for CFI.
SLUGOWNER=${TRAVIS_REPO_SLUG%/*}
if [[ "$SLUGOWNER" == "" ]]; then
  SLUGOWNER=opprop
fi
if [ ! -d ../do-like-javac ] ; then
    (cd $JSR308 && git clone https://github.com/${SLUGOWNER}/do-like-javac.git)
fi

# Build CFI Test Lib jar
(cd $JSR308/checker-framework-inference && ./gradlew testLibJar)

# Running test suite
./gradlew test --console=plain

# Check Units Proof
# TODO: This requires ocaml and camlp5 in travis environment, which means we need to build a docker
# ./coq-proof/setup-coq.sh
# ./coq-proof/compile.sh

# Running Units Inference on working benchmarks
./benchmarks/run-travis-benchmarks.sh travis

# Print summary stats
./experiment-tools/gen-inference-summary.sh benchmarks/travis-benchmarks
