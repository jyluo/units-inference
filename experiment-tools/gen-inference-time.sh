#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script gives the overall inference time taken in a table format"
    echo "usage: $0 <corpus-root-folder-name> <time-log-file>"
    exit 1
    # in benchmark folder
    # gen-inference-time.sh projects projectsTimeLog.txt
fi

WORKING_DIR=$(cd $(dirname "$0") && pwd)

TIMEFILE=$(cd .; pwd)/$2

cd $1

declare -a projects=($(ls -d */ | sort))

cd $WORKING_DIR

echo -e "Project \t Overall Time (sec)"

for project in "${projects[@]}"; do
    # print project name without trailing slash
    project=$(printf '%*.*s' 0 $((${#project} - 1)) "$project")

    # echo $project
    grep "Time taken by $project" "$TIMEFILE" | \
        cut -d ':' -f 2 | cut -d ' ' -f 2 | \
        sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' | \
        xargs echo -e "$project \t"
done

printf '\n'
