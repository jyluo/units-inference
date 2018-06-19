#!/bin/bash

set -e

WORKING_DIR=$(pwd)

ROOT=$(cd $(dirname "$0")/.. && pwd)

if [ -z "${JSR308}" ] ; then
    export JSR308=$(cd ${ROOT}/.. && pwd)
fi

DLJC="${JSR308}/do-like-javac"
export AFU="${JSR308}/annotation-tools/annotation-file-utilities"
export PATH="${PATH}:${AFU}/scripts"

CFI="${ROOT}/checker-framework-inference"
UI="${ROOT}/units-inference"
libDir="${CFI}/lib"

export CLASSPATH="${UI}/build/classes/java/main:${UI}/build/libs/units-inference.jar:."

export DYLD_LIBRARY_PATH="${libDir}"
export LD_LIBRARY_PATH="${libDir}"

CHECKER=units.UnitsChecker
SOLVER=units.solvers.backend.UnitsSolverEngine
DEBUG_SOLVER=checkers.inference.solver.DebugSolver

#parsing build command of the target program
build_cmd="$1"
shift
while [ "$#" -gt 0 ]
do
    build_cmd="$build_cmd $1"
    shift
done

cd "$WORKING_DIR"

infer_cmd="python $DLJC/dljc -t inference --crashExit --checker $CHECKER --solver $SOLVER --solverArgs=\"collectStatistic=true\" -o logs --mode=\"INFER\" -afud $WORKING_DIR/annotated -- $build_cmd "

# debug_onlyCompile="--onlyCompileBytecodeBase true"
# debug_cmd="python $DLJC/dljc -t testminimizer --annotationClassPath $JSR308/units-inference/bin $debug_onlyCompile --expectOutputRegex 'Unsatisfiable' --checker $CHECKER --solver $SOLVER --solverArgs=\"collectStatistic=true,solver=Z3Int\" -o logs -m INFER -afud $WORKING_DIR/annotated -- $build_cmd "
debug_cmd="python $DLJC/dljc -t inference --crashExit --checker $CHECKER --solver $DEBUG_SOLVER --solverArgs=\"collectStatistic=true\" -o logs --mode=\"ROUNDTRIP\" -afud $WORKING_DIR/annotated -- $build_cmd "

#running_cmd=$infer_cmd
running_cmd=$infer_cmd

echo "============ Important variables ============="
echo "JSR308: $JSR308"
echo "CLASSPATH: $CLASSPATH"
echo "build cmd: $build_cmd"
echo "running cmd: $running_cmd"
echo "============================================="

eval "$running_cmd"

echo "---- Reminder: do not forget to clean up the project! ----"
