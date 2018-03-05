#!/bin/bash

ROOT=$(cd $(dirname "$0")/.. && pwd)

echo "$ROOT"/units-inference/bin

CFI="$ROOT"/checker-framework-inference

CHECKER=units.UnitsChecker

DEBUG_SOLVER=checkers.inference.solver.DebugSolver

IS_HACK=true

export CLASSPATH="$ROOT"/units-inference/bin:"$ROOT"/units-inference/dist/units-inference.jar:.
export external_checker_classpath="$ROOT"/units-inference/bin:"$ROOT"/units-inference/dist/units-inference.jar

# Inference
$CFI/scripts/inference-dev -m ROUNDTRIP --checker "$CHECKER" --solver "$DEBUG_SOLVER" --solverArgs="collectStatistic=true" --hacks="$IS_HACK" -afud ./annotated "$@"
