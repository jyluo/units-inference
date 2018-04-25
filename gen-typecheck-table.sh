#!/bin/bash

declare -a statsKeys=("error: \[assignment.type.incompatible" \
    "error: \[argument.type.incompatible" \
    "error: \[return.type.incompatible" )

cd ./$1

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

# Print header row
printf 'Project\t'
for key in "${statsKeys[@]}"; do
    printf '%s\t' "$key"
done
printf '\n'

# Print each project
for project in "${projects[@]}"; do
    # print project name without trailing slash
    printf '%*.*s\t' 0 $((${#project} - 1)) "$project"

    if [ -f $project/logs/infer.log ]; then
        for key in "${statsKeys[@]}"; do
            count=$(grep "$key" "$project/logs/infer.log" | wc -l)
            printf '%s\t' "$count"
        done
    else
        for key in "${statsKeys[@]}"; do
            printf '%s\t' "0"
        done
    fi

    printf '\n'

done

printf '\n'

# TODO: LOCs