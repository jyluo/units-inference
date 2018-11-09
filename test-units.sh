#!/bin/bash

# Failed the whole script if any command failed
set -e

# Running test suite
./gradlew test --console=plain

WORKING_DIR=$(pwd)

if [ -z "${JSR308}" ] ; then
    export JSR308=$(cd $(dirname "$0")/.. && pwd)
fi

# Pull DLJC if it doesn't exist
# This is for downstream travis test for CFI.
SLUGOWNER=${TRAVIS_REPO_SLUG%/*}
if [[ "$SLUGOWNER" == "" ]]; then
  SLUGOWNER=opprop
fi
if [ ! -d ../do-like-javac ] ; then
    (cd $JSR308 && git clone https://github.com/${SLUGOWNER}/do-like-javac.git)
fi

./run-travis-benchmarks.sh travis
