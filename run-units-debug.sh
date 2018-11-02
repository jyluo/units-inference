#!/bin/bash

JSR308=$(cd $(dirname "$0")/.. && pwd)

echo "$JSR308"/units-inference

CFI=$JSR308/checker-framework-inference
UI=$JSR308/units-inference
UIPATH=$UI/build/classes/java/main:$UI/build/resources/main:$UI/build/libs/units-inference.jar

export AFU=$JSR308/annotation-tools/annotation-file-utilities
export PATH=$AFU/scripts:$PATH

CHECKER=units.UnitsChecker

DEBUG_SOLVER=checkers.inference.solver.DebugSolver
SOLVERARGS="collectStatistics=true,writeSolutions=true,noAppend=true"

IS_HACK=true

export CLASSPATH=$UIPATH:.
export external_checker_classpath=$UIPATH

# Inference
$CFI/scripts/inference-dev -m ROUNDTRIP --checker "$CHECKER" \
    --solver "$DEBUG_SOLVER" --solverArgs=$SOLVERARGS \
    --hacks="$IS_HACK" -afud ./annotated "$@"
