#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script gives the language feature usage statistics from the inference outputs of a corpus"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

cd $1

declare -a statsKeys=(
    "Made arithmetic + constraint:" \
    "Made arithmetic - constraint:" \
    "Made arithmetic \* constraint:" \
    "Made arithmetic / constraint:" \
    "Made arithmetic % constraint:" \
    "Made comparison constraint:" )

declare -a methodKeys=(
    "visited: java.lang.System.currentTimeMillis" \
    "visited: java.lang.System.nanoTime" \
    "visited: java.lang.Thread.sleep" \
    "visited: java.lang.Math.cos" \
    "visited: java.lang.Math.sin" \
    "visited: java.lang.Math.tan" \
    "visited: java.lang.Math.asin" \
    "visited: java.lang.Math.acos" \
    "visited: java.lang.Math.atan" \
    "visited: java.lang.Math.atan2" \
    "visited: java.lang.Math.sinh" \
    "visited: java.lang.Math.cosh" \
    "visited: java.lang.Math.tanh" \
    "visited: java.lang.Math.toDegrees" \
    "visited: java.lang.Math.toRadians"
    )

declare -a headers=(
    " +" \
    "-" \
    "*" \
    "/" \
    "%" \
    "compare" \
    "currentTimeMillis" \
    "nanoTime" \
    "sleep" \
    "cos" \
    "sin" \
    "tan" \
    "asin" \
    "acos" \
    "atan" \
    "atan2" \
    "sinh" \
    "cosh" \
    "tanh" \
    "toDegrees" \
    "toRadians" )

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

# Print header row
printf 'Project\t'
for key in "${headers[@]}"; do
    printf '%s\t' "$key"
done
printf '\n'

# Print each project
for project in "${projects[@]}"; do
    # print project name without trailing slash
    printf '%*.*s\t' 0 $((${#project} - 1)) "$project"

    if [ -f $project/logs/infer.log ]; then
        for key in "${statsKeys[@]}"; do
            grep -w "$key" "$project/logs/infer.log" | cut -d ':' -f 2 | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done

        for key in "${methodKeys[@]}"; do
            grep -w "$key" "$project/logs/infer.log" | wc -l | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done
    else
        for key in "${statsKeys[@]}"; do
            printf '%s\t' "0"
        done

        for key in "${methodKeys[@]}"; do
            printf '%s\t' "0"
        done
    fi

    printf '\n'
done

printf '\n'

# TODO: LOCs