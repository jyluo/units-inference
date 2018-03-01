#!/bin/bash

ROOT=$(cd $(dirname "$0")/.. && pwd)

echo "$ROOT"/units-inference/bin

CFI="$ROOT"/checker-framework-inference

CHECKER=units.UnitsChecker

SOLVER=units.solvers.backend.UnitsSolverEngine

# DEBUG_SOLVER=checkers.inference.solver.DebugSolver

IS_HACK=true

# Debug
# SOLVER="$DEBUG_SOLVER"
# IS_HACK=false

export CLASSPATH="$ROOT"/units-inference/src/units:"$ROOT"/units-inference/bin:.
export external_checker_classpath="$ROOT"/units-inference/src/units:"$ROOT"/units-inference/bin

# Inference
# $CFI/scripts/inference-dev --checker "$CHECKER" --solver "$SOLVER" --solverArgs="collectStatistic=true,solver=Z3Int" --hacks="$IS_HACK" -m ROUNDTRIP -afud ./annotated "$@"

# TYPE CHECKING
$CFI/scripts/inference -m TYPECHECK --checker "$CHECKER" --cfArgs="-AprintErrorStack" "$@"