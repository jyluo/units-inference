#!/bin/bash

TESTFILE=testing/inference/VectorInfer.java
ANNOTATEDFILE=annotated/VectorInfer.java

subl $TESTFILE

./scripts/run-units-infer.sh $TESTFILE

subl $ANNOTATEDFILE
