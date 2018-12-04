#!/bin/bash

JSR308=$(cd $(dirname "$0")/../.. && pwd)

echo "$JSR308"/units-inference

CFI=$JSR308/checker-framework-inference
UI=$JSR308/units-inference
UIPATH=$UI/build/classes/java/main:$UI/build/resources/main:$UI/build/libs/units-inference.jar

CHECKER=units.UnitsChecker

export CLASSPATH=$UIPATH:.
export external_checker_classpath=$UIPATH

# TYPE CHECKING
$CFI/scripts/inference -m TYPECHECK --checker "$CHECKER" \
    --targetclasspath "$CLASSPATH" "$@"
