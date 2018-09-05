#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script gives the overall inference summary statistics from a corpus in a tabular format"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

cd $1

declare -a statsKeys=("slots_size" "constraint_size" \
    "constantslot" "variableslot" \
    "subtypeconstraint" "equalityconstraint" "arithmeticconstraint" "comparableconstraint" "existentialconstraint" "preferenceconstraint")

declare -a constantSlotsNameKeys=("Top" "Dimensionless" "Bottom" "m" "m2" "s" "ms" "ns" "mPERs" "deg" "rad" "other")

declare -a constantSlotsOutputKeys=("Annotation: @UnknownUnits" "Annotation: @Dimensionless" "Annotation: @UnitsBottom" \
    "Annotation: @m" "Annotation: @m2" "Annotation: @s" "Annotation: @ms" "Annotation: @ns" "Annotation: @mPERs" "Annotation: @deg" "Annotation: @rad")

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

# Print header row
printf 'Project\tinference failed\texpected-subtargets\tsuccessful-subtargets\tserialization-time\tsolving-time\tz3-bools\tz3-ints\tz3-asserts\tz3-assert-softs\t'
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

    if [ -f $project/logs/infer.log ]; then
        # inference success?
        count=$(grep -w "!!! The set of constraints is unsatisfiable! !!!" "$project/logs/infer.log" | wc -l)
        printf '%s\t' "$count"
        # number of sub-projects
        count=$(grep -w "Running java" "$project/logs/infer.log" | wc -l)
        printf '%s\t' "$count"
        # number of successful sub-projects
        count=$(grep -w "Statistic start" "$project/logs/infer.log" | wc -l)
        printf '%s\t' "$count"
        # serialization time
        grep -w "SMT Serialization Time" "$project/logs/infer.log" | cut -d ':' -f 2 | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        # solving time
        grep -w "SMT Solving Time" "$project/logs/infer.log" | cut -d ':' -f 2 | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
    else
        printf '%s\t' "1"
        printf '%s\t' "0"
        printf '%s\t' "0"
        printf '%s\t' "0"
        printf '%s\t' "0"
    fi

    if [ -f $project/z3ConstraintStats.smt ]; then
        # number of z3 bools
        count=$(grep "declare-fun.*Bool" "$project/z3ConstraintStats.smt" | wc -l)
        printf '%s\t' "$count"
        # number of z3 ints
        count=$(grep "declare-fun.*Int" "$project/z3ConstraintStats.smt" | wc -l)
        printf '%s\t' "$count"
        # number of z3 asserts
        count=$(grep -w "assert" "$project/z3ConstraintStats.smt" | wc -l)
        printf '%s\t' "$count"
        # number of z3 assert-softs
        count=$(grep -w "assert-soft" "$project/z3ConstraintStats.smt" | wc -l)
        printf '%s\t' "$count"
    else
        printf '%s\t' "0"
        printf '%s\t' "0"
        printf '%s\t' "0"
        printf '%s\t' "0"
    fi

    if [ -f $project/statistic.txt ]; then
        for key in "${statsKeys[@]}"; do
            # sift through the log files to find all the statistics values, sum them up and print it
            grep -w "$key" "$project/statistic.txt" | cut -d ',' -f 2 | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done
    else
        for key in "${statsKeys[@]}"; do
            printf '%s\t' "0"
        done
    fi

    if [ -f $project/solutions.txt ]; then
        for key in "${constantSlotsOutputKeys[@]}"; do
            # sift through the log files to find all the constant slot output values, sum them up and print it
            grep -w "$key" "$project/solutions.txt" | wc -l | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done

        grep "Annotation: @UnitsInternal(" "$project/solutions.txt" | wc -l | \
            awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
    else
        for key in "${constantSlotsOutputKeys[@]}"; do
            printf '%s\t' "0"
        done

        printf '%s\t' "0"
    fi

    printf '\n'
done

printf '\n'

# TODO: LOCs