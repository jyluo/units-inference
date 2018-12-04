#!/bin/bash

JSR308=$(cd $(dirname "$0")/../.. && pwd)

echo "$JSR308"/units-inference

CFI=$JSR308/checker-framework-inference
UI=$JSR308/units-inference
UIPATH=$UI/build/classes/java/main:$UI/build/resources/main:$UI/build/libs/units-inference.jar

export AFU=$JSR308/annotation-tools/annotation-file-utilities
export PATH=$AFU/scripts:$PATH

CHECKER=units.UnitsChecker

SOLVER=units.solvers.backend.UnitsSolverEngine
if [ -n "$1" ] && [ $1 = "gauss" ]; then
    SOLVERARGS=solver=GJE,collectStatistics=true,writeSolutions=true,noAppend=true
else
    SOLVERARGS=solver=Z3smt,collectStatistics=true,writeSolutions=true,noAppend=true
fi

IS_HACK=true

export CLASSPATH=$UIPATH:.
export external_checker_classpath=$UIPATH

# Inference
if [ -n "$1" ] && [ $1 = "gauss" ]; then
    $CFI/scripts/inference-dev -m ROUNDTRIP --checker "$CHECKER" \
        --solver "$SOLVER" --solverArgs="$SOLVERARGS" \
        --hacks="$IS_HACK" -afud ./annotated "${@:2}"
else
    $CFI/scripts/inference-dev -m ROUNDTRIP --checker "$CHECKER" \
        --solver "$SOLVER" --solverArgs="$SOLVERARGS" \
        --hacks="$IS_HACK" -afud ./annotated "$@"
fi
