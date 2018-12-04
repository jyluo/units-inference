#!/bin/bash

TESTFILE=testing/inference/VectorInfer.java
ANNOTATEDFILE=annotated/VectorInfer.java

subl $TESTFILE

./run-units-infer.sh $TESTFILE

subl $ANNOTATEDFILE
