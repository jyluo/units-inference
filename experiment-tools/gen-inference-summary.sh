#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script gives the overall inference summary statistics from a corpus in a human readable format"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

declare -a statsKeys=("slots_size" "constraint_size" \
    "constantslot" "variableslot" \
    "subtypeconstraint" "arithmeticconstraint" "equalityconstraint" "existentialconstraint" "preferenceconstraint")

cd $1

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

for project in "${projects[@]}"; do
    # print project name without trailing slash
    printf '\n%*.*s\n' 0 $((${#project} - 1)) "$project"

    # number of sub-projects
    countKey="  expected-subtargets"
    padding=$(printf '%*.*s' 0 $((padlength - ${#countKey})) "$pad")
    count=$(grep "Running java" "$project/logs/infer.log" | wc -l)
    echo -e "$countKey$padding\t$count"
    # number of successful sub-projects
    countKey="  successful-subtargets"
    padding=$(printf '%*.*s' 0 $((padlength - ${#countKey})) "$pad")
    count=$(grep "Statistic start" "$project/logs/infer.log" | wc -l)
    echo -e "$countKey$padding\t$count"

    for key in "${statsKeys[@]}"; do
        # string consisting of the stats key and the count
        keyArg="  ${key}"
        # string consisting of the stats key, count, and space padding to 30 total characters
        padding=$(printf '%*.*s' 0 $((padlength - ${#keyArg})) "$pad")
        # sift through the log files to find all the statistics values, sum them up and print it
        grep "$key" "$project/logs/infer.log" | cut -d ',' -f 2 | \
            awk -v p="${keyArg}${padding}\t" '{sum += $1} END {print p sum}'
    done
done

printf '\n'
