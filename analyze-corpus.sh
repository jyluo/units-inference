#!/bin/bash

declare -a statsKeys=("slots_size" "constraint_size" \
    "constantslot" "variableslot" \
    "subtypeconstraint" "arithmeticconstraint" "equalityconstraint" "existentialconstraint" "preferenceconstraint")

cd ./corpus

declare -a projects=($(ls -d */))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

for project in "${projects[@]}"; do
    # print project name without trailing slash
    printf '\n%*.*s\n' 0 $((${#project} - 1)) "$project"

    for key in "${statsKeys[@]}"; do
        # number of sub-projects
        count=$(grep "$key" "$project/logs/infer.log" | wc -l)
        # string consisting of the stats key and the count
        keyArg="  ${key} (${count}) ="
        # string consisting of the stats key, count, and space padding to 30 total characters
        prefix=$(printf '%*.*s' 0 $((padlength - ${#keyArg})) "$pad")
        # sift through the log files to find all the statistics values, sum them up and print it
        grep "$key" "$project/logs/infer.log" | cut -d ',' -f 2 | \
            awk -v p="${keyArg}${prefix}" '{sum += $1} END {print p sum}'
    done
done

printf '\n'
