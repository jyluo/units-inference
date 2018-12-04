#!/bin/bash

TESTFILE=testing/typecheck/Speeds.java

subl $TESTFILE

./scripts/run-units-typecheck.sh $TESTFILE
