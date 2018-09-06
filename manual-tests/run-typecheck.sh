#!/bin/bash
current_dir=$(cd .; pwd)

if [[ $1 == /* ]]; then
    file=$1
else
    file="${current_dir}/"$1
fi

# ../run-units-typecheck.sh "${current_dir}/"$1
../run-units-typecheck.sh "${file}"
