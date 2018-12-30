#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script gives the overall inference summary statistics from a corpus in a tabular format"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

cd $1

declare -a insertedAnnotationKeys=(
    "UnknownUnits" \
    "UnitsBottom" )

declare -a projects=($(ls -d */ | sort))

# Helper functions =============================================================

# Print each project ===========================================================
for project in "${projects[@]}"; do
    # remove trailing slash in project name
    project=$(printf '%*.*s' 0 $((${#project} - 1)) "$project")

    printf '%s\n' "$project"

    INSERTKey=insert-annotation
    QUALPrefix=@units.qual.
    if [ -f "$project/logs/infer_result_0.jaif" ]; then
        for key in "${insertedAnnotationKeys[@]}"; do
            # there can be more than 1 result jaif file
            grep -oh "insert-annotation.*$key" $project/logs/infer_result_*.jaif | sort | uniq
        done
    fi

    printf '\n'
done
