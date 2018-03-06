#!/bin/bash
current_dir=$(cd .; pwd)

if [[ $1 == /* ]]; then
    file=$1
else
    file="${current_dir}/"$1
fi

# has to be executed from ~/jsr308/units-inference/bin because classpath isn't being properly handled
cd ../bin
# ../run-units-typecheck.sh "${current_dir}/"$1
../run-units-typecheck.sh --cfArgs="-AprintErrorStack=true" "${file}"
