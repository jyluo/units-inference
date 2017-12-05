#!/bin/bash

ROOT=$(cd $(dirname "$0")/.. && pwd)

echo "$ROOT"/units-inference/bin

CFI="$ROOT"/checker-framework-inference

SOLVER=units.solvers.backend.UnitsSolverEngine

DEBUG_SOVLER=checkers.inference.solver.DebugSolver

IS_HACK=true

CHECKER=units.UnitsChecker

# SOLVER="$DEBUG_SOVLER"
# IS_HACK=false
DEBUG_CLASSPATH=""

export CLASSPATH="$ROOT"/units-inference/bin:$DEBUG_CLASSPATH:.
export external_checker_classpath="$ROOT"/units-inference/bin

$CFI/scripts/inference-dev --checker "$CHECKER" --solver "$SOLVER" --solverArgs="collectStatistic=true,solver=Z3Int" --hacks="$IS_HACK" -m ROUNDTRIP -afud ./annotated "$@"

# TYPE CHECKING
# $CFI/scripts/inference-dev --checker "$CHECKER" --solver "$SOLVER" --solverArgs="collectStatistic=true,solver=z3" --hacks="$IS_HACK" -m TYPECHECK "$@"