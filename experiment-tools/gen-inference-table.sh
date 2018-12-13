#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script gives the overall inference summary statistics from a corpus in a tabular format"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

cd $1

declare -a statsTimeKeys=(
    "smt_serialization_time(millisec)" \
    "smt_solving_time(millisec)" \
    "smt_unsat_serialization_time(millisec)" \
    "smt_unsat_solving_time(millisec)")

declare -a statsKeys=(
    "total_slots" "total_constraints" \
    "constantslot" "total_variable_slots" \
    "subtypeconstraint" "equalityconstraint" "arithmeticconstraint" \
    "comparableconstraint" "existentialconstraint" "preferenceconstraint")

declare -a constantSlotsNameKeys=(
    "Top" "Dimensionless" "Bottom" "m" "m2" "s" \
    "ms" "ns" "mPERs" "deg" "rad" "other")

declare -a constantSlotsOutputKeys=(
    "Annotation: @UnknownUnits" \
    "Annotation: @Dimensionless" "Annotation: @UnitsBottom" \
    "Annotation: @m" "Annotation: @m2" "Annotation: @s" "Annotation: @ms" \
    "Annotation: @ns" "Annotation: @mPERs" "Annotation: @deg" \
    "Annotation: @rad")

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

# Print header row
printf 'Project\tinference failed\texpected-subtargets\tsuccessful-subtargets\tserialization-time(ms)\tsolving-time(ms)\tunsat-serialization-time(ms)\tunsat-solving-time(ms)\tz3-bools\tz3-ints\tz3-asserts\tz3-assert-softs\t'
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
        count=$(grep -w "Statistics have been written to" "$project/logs/infer.log" | wc -l)
        printf '%s\t' "$count"
    else
        printf '%s\t' "1"
        printf '%s\t' "0"
        printf '%s\t' "0"
    fi

    InferenceStatsFile=$project/statistics.txt
    if [ -f $InferenceStatsFile ]; then
        for key in "${statsTimeKeys[@]}"; do
            # sift through the log files to find all the statistics values, sum them up and print it
            grep -w "$key" "$InferenceStatsFile" | cut -d ':' -f 2 | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done
    else
        for key in "${statsTimeKeys[@]}"; do
            printf '%s\t' "0"
        done
    fi

    ConstraintsStatsFile=$project/z3ConstraintsGlob.smt
    if [ -f $ConstraintsStatsFile ]; then
        # number of z3 bools
        count=$(grep "declare-fun.*Bool" "$ConstraintsStatsFile" | wc -l)
        printf '%s\t' "$count"
        # number of z3 ints
        count=$(grep "declare-fun.*Int" "$ConstraintsStatsFile" | wc -l)
        printf '%s\t' "$count"
        # number of z3 asserts
        count=$(grep -w "assert" "$ConstraintsStatsFile" | wc -l)
        printf '%s\t' "$count"
        # number of z3 assert-softs
        count=$(grep -w "assert-soft" "$ConstraintsStatsFile" | wc -l)
        printf '%s\t' "$count"
    else
        printf '%s\t' "0"
        printf '%s\t' "0"
        printf '%s\t' "0"
        printf '%s\t' "0"
    fi

    if [ -f $InferenceStatsFile ]; then
        for key in "${statsKeys[@]}"; do
            # sift through the log files to find all the statistics values, sum them up and print it
            grep -w "$key" "$InferenceStatsFile" | cut -d ':' -f 2 | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done
    else
        for key in "${statsKeys[@]}"; do
            printf '%s\t' "0"
        done
    fi

    InferenceSolutionsFile=$project/solutions.txt
    if [ -f $project/solutions.txt ]; then
        for key in "${constantSlotsOutputKeys[@]}"; do
            # sift through the log files to find all the constant slot output values, sum them up and print it
            grep -w "$key" "$InferenceSolutionsFile" | wc -l | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done

        grep "Annotation: @UnitsInternal(" "$InferenceSolutionsFile" | wc -l | \
            awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
    else
        for key in "${constantSlotsOutputKeys[@]}"; do
            printf '%s\t' "0"
        done

        printf '%s\t' "0"
    fi

    printf '\n'
done
