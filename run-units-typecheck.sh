#!/bin/bash

ROOT=$(cd $(dirname "$0")/.. && pwd)

echo "$ROOT"/units-inference

CFI="${ROOT}/checker-framework-inference"
UI="${ROOT}/units-inference"

CHECKER=units.UnitsChecker

export CLASSPATH="${UI}/build/classes/java/main:${UI}/build/libs/units-inference.jar:."
export external_checker_classpath="${UI}/build/classes/java/main:${UI}/build/resources/main:${UI}/build/libs/units-inference.jar"

# TYPE CHECKING
$CFI/scripts/inference -m TYPECHECK --checker "$CHECKER" --targetclasspath "$CLASSPATH" --cfArgs "-AprintErrorStack" "$@"