#!/bin/bash

TESTFILE=testing/typecheck/Speeds.java

subl $TESTFILE

./run-units-typecheck.sh $TESTFILE

