#!/bin/bash

set -e

WORKING_DIR=$(pwd)
JSR308=$(cd $(dirname "$0")/.. && pwd)

CFI=$JSR308/checker-framework-inference
UI=$JSR308/units-inference
UIPATH=$UI/build/classes/java/main:$UI/build/resources/main:$UI/build/libs/units-inference.jar

export AFU=$JSR308/annotation-tools/annotation-file-utilities
export PATH=$AFU/scripts:$PATH
export CLASSPATH=$UIPATH
export external_checker_classpath=$UIPATH

CFI_LIB=$CFI/lib
export DYLD_LIBRARY_PATH=$CFI_LIB
export LD_LIBRARY_PATH=$CFI_LIB

CHECKER=units.UnitsChecker
SOLVER=units.solvers.backend.UnitsSolverEngine
# DEBUG_SOLVER=checkers.inference.solver.DebugSolver
SOLVERARGS="solver=Z3smt,collectStatistics=true,writeSolutions=true,noAppend=true"

DLJC=$JSR308/do-like-javac

# Parsing build command of the target program
build_cmd="$1"
shift
while [ "$#" -gt 0 ]
do
    build_cmd="$build_cmd $1"
    shift
done

# DLJC Inference
cd "$WORKING_DIR"

infer_cmd="python $DLJC/dljc -t inference --guess --crashExit \
--checker $CHECKER --solver $SOLVER --solverArgs=$SOLVERARGS \
-o logs -m INFER -afud $WORKING_DIR/annotated -- $build_cmd "

# debug_onlyCompile="--onlyCompileBytecodeBase true"
# TODO:see how ontology uses testminimizer
# debug_cmd="python $DLJC/dljc -t testminimizer --annotationClassPath $UIPATH \
# $debug_onlyCompile --expectOutputRegex 'Unsatisfiable' --checker $CHECKER \
# --solver $DEBUG_SOLVER --solverArgs=$SOLVERARGS \
# -o logs -m INFER -afud $WORKING_DIR/annotated -- $build_cmd "
debug_cmd="python $DLJC/dljc -t inference --guess --crashExit \
--checker $CHECKER --solver $DEBUG_SOLVER --solverArgs=$SOLVERARGS \
-o logs -m ROUNDTRIP -afud $WORKING_DIR/annotated -- $build_cmd "

running_cmd=$infer_cmd

echo "============ Important variables ============="
echo "JSR308: $JSR308"
echo "CLASSPATH: $CLASSPATH"
echo "build cmd: $build_cmd"
echo "running cmd: $running_cmd"
echo "============================================="

eval "$running_cmd"

echo "---- Reminder: do not forget to clean up the project! ----"
