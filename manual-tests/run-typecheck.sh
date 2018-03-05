#!/bin/bash
current_dir=$(cd .; pwd)
# has to be executed from ~/jsr308/units-inference/bin because classpath isn't being properly handled
cd ../bin
# ../run-units-typecheck.sh "${current_dir}/"$1
../run-units-typecheck.sh --cfArgs="-AprintErrorStack=true" "${current_dir}/"$1
