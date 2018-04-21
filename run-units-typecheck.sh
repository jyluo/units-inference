#!/bin/bash

ROOT=$(cd $(dirname "$0")/.. && pwd)

echo "$ROOT"/units-inference/bin

CFI="$ROOT"/checker-framework-inference

CHECKER=units.UnitsChecker

export CLASSPATH="$ROOT"/units-inference/bin:"$ROOT"/units-inference/dist/units-inference.jar:.
export external_checker_classpath="$ROOT"/units-inference/bin:"$ROOT"/units-inference/dist/units-inference.jar

# TYPE CHECKING
$CFI/scripts/inference -m TYPECHECK --checker "$CHECKER" --targetclasspath "$CLASSPATH" --cfArgs "-AprintErrorStack" "$@"