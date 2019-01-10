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

# overall tabulation

echo ""

echo "Overall locations"

grep -r "insert-annotation.*@units" --include=*.jaif | cut -d : -f2 | rev | cut -d , -f 1 | rev | sed 's/insert-annotation//g' | sort | uniq -c | sort -nr | sed -r 's/[ ]*([0-9]+)(.*)$/\1 \t \2/p' | uniq | head -10

echo ""

echo "Non-dimensionless locations"

grep -r "insert-annotation.*@units" --include=*.jaif | grep -v "Dimensionless" | cut -d : -f2 | rev | cut -d , -f 1 | rev | sed 's/insert-annotation//g' | sort | uniq -c | sort -nr | sed -r 's/[ ]*([0-9]+)(.*)$/\1 \t \2/p' | uniq | head -10

echo ""

echo "Tops locations"

grep -r "insert-annotation.*@units.qual.UnknownUnits" --include=*.jaif | cut -d : -f2 | rev | cut -d , -f 1 | rev | sed 's/insert-annotation//g' | sort | uniq -c | sort -nr | sed -r 's/[ ]*([0-9]+)(.*)$/\1 \t \2/p' | uniq | head -10

echo ""

echo "Bots locations"

grep -r "insert-annotation.*@units.qual.UnitsBottom" --include=*.jaif | cut -d : -f2 | rev | cut -d , -f 1 | rev | sed 's/insert-annotation//g' | sort | uniq -c | sort -nr | sed -r 's/[ ]*([0-9]+)(.*)$/\1 \t \2/p' | uniq | head -10

echo ""


# grep -r "insert-annotation.*@unit" --include=*.jaif | cut -d : -f2 | rev | cut -d , -f 1 | rev | sed 's/insert-annotation//g' | sort | uniq -c | sort -nr | sed -r 's/[ ]*([0-9]+)(.*)$/\1 \t \2/p'

# # Print each project ===========================================================
# for project in "${projects[@]}"; do
#     # remove trailing slash in project name
#     project=$(printf '%*.*s' 0 $((${#project} - 1)) "$project")

#     printf '%s\n' "$project"

#     INSERTKey=insert-annotation
#     QUALPrefix=@units.qual.
#     if [ -f "$project/logs/infer_result_0.jaif" ]; then
#         for key in "${insertedAnnotationKeys[@]}"; do
#             # there can be more than 1 result jaif file
#             grep -oh "insert-annotation.*$key" $project/logs/infer_result_*.jaif | sort | uniq

#             grep -r "insert-annotation.*@unit" --include=*.jaif | cut -d : -f2 | rev | cut -d , -f 1 | rev | sed 's/insert-annotation//g' | sort | uniq -c | sort -nr | sed -r 's/[ ]*([0-9]+)(.*)$/\1 \t \2/p'


#         done
#     fi

#     printf '\n'
# done
