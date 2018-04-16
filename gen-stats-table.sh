#!/bin/bash

declare -a statsKeys=("slots_size" "constraint_size" \
    "constantslot" "variableslot" \
    "subtypeconstraint" "arithmeticconstraint" "equalityconstraint" "existentialconstraint" "preferenceconstraint")

declare -a constantSlotsNameKeys=("Top" "Dimensionless" "Bottom" "ms" "ns" "deg" "rad")

declare -a constantSlotsOutputKeys=("Annotation: @UnknownUnits" "Annotation: @Dimensionless" "Annotation: @UnitsBottom" \
    "Annotation: @ms" "Annotation: @ns" "deg" "rad")

cd ./$1

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

# Print header row
printf 'Project\tinference failed\texpected-subtargets\tsuccessful-subtargets\t'
for key in "${statsKeys[@]}"; do
    printf '%s\t' "$key"
done
for key in "${constantSlotsNameKeys[@]}"; do
    printf '%s\t' "$key"
done
printf '\n'

# Print each project
for project in "${projects[@]}"; do
    # print project name without trailing slash
    printf '%*.*s\t' 0 $((${#project} - 1)) "$project"

    # inference success?
    count=$(grep "!!! The set of constraints is unsatisfiable! !!!" "$project/logs/infer.log" | wc -l)
    printf '%s\t' "$count"
    # number of sub-projects
    count=$(grep "Running java" "$project/logs/infer.log" | wc -l)
    printf '%s\t' "$count"
    # number of successful sub-projects
    count=$(grep "Statistic start" "$project/logs/infer.log" | wc -l)
    printf '%s\t' "$count"

    for key in "${statsKeys[@]}"; do
        # sift through the log files to find all the statistics values, sum them up and print it
        grep "$key" "$project/statistic.txt" | cut -d ',' -f 2 | \
            awk -v tab="\t" '{sum += $1} END {printf sum tab}'
    done

    for key in "${constantSlotsOutputKeys[@]}"; do
        # sift through the log files to find all the constant slot output values, sum them up and print it
        grep "$key" "$project/solutions.txt" | wc -l | \
            awk -v tab="\t" '{sum += $1} END {printf sum tab}'
    done

    printf '\n'
done

printf '\n'

# TODO: LOCs