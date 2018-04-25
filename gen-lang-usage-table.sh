#!/bin/bash

declare -a statsKeys=("currentTimeMillis()" "nanoTime()" \
    "Thread.sleep(" \
    "Math.cos(" "Math.sin(" "Math.tan(" \
    "Math.asin(" "Math.acos(" "Math.atan(" "Math.atan2(" \
    "Math.sinh(" "Math.cosh(" "Math.tanh(" \
    "Math.toDegrees(" "Math.toRadians(" \
    "\w + \w" \
    "\w - \w" \
    "\w \* \w" \
    "\w / \w" \
    "\w % \w" \
    "\w < \w" \
    "\w > \w" \
    "\w <= \w" \
    "\w >= \w" \
    "\w == \w" \
    "\w != \w" )

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

    cd $project

    for key in "${statsKeys[@]}"; do
        count=$(grep -r "$key" --include=*.java | wc -l)
        printf '%s\t' "$count"
    done

    printf '\n'

    cd ../

done

printf '\n'

# TODO: LOCs