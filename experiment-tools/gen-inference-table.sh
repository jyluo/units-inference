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
    "UnknownUnits" \
    "Dimensionless" "UnitsBottom" \
    "m" "m2" "s" "ms" \
    "ns" "mPERs" "deg" \
    "rad")

declare -a insertedAnnotationKeys=(
    "UnknownUnits" \
    "Dimensionless" "UnitsBottom" \
    "m" "m2" "s" "ms" \
    "ns" "mPERs" "deg" \
    "rad" \
    "UnitsRep")

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

# Print header row
declare -a headers=(
    'Project' \
    'inference-failed' \
    'expected-subtargets' \
    'successful-subtargets' \
    'serialization-time(ms)' \
    'solving-time(ms)' \
    'unsat-serialization-time(ms)' \
    'unsat-solving-time(ms)' \
    'process-time(sec)'\
    'z3-bools' \
    'z3-ints' \
    'z3-asserts' \
    'z3-assert-softs')

for key in "${headers[@]}"; do
    printf '%s\t' "$key"
done
for key in "${statsKeys[@]}"; do
    printf '%s\t' "$key"
done
for key in "${constantSlotsNameKeys[@]}"; do
    printf '%s\t' "$key"
done

printf '%s\t' "inserted-annotations"
for key in "${insertedAnnotationKeys[@]}"; do
    printf '%s\t' "$key"
done

printf '\n'

# Print each project
for project in "${projects[@]}"; do
    # remove trailing slash in project name
    project=$(printf '%*.*s' 0 $((${#project} - 1)) "$project")

    printf '%s\t' "$project"

    InferenceLogFile=$project/logs/infer.log
    if [ -f $InferenceLogFile ]; then
        # inference success?
        count=$(grep -w "!!! The set of constraints is unsatisfiable! !!!" "$InferenceLogFile" | wc -l)
        printf '%s\t' "$count"
        # number of sub-projects
        count=$(grep -w "Running java" "$InferenceLogFile" | wc -l)
        printf '%s\t' "$count"
        # number of successful sub-projects
        count=$(grep -w "Statistics have been written to" "$InferenceLogFile" | wc -l)
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

    InferenceTimingFile=$project/inferTiming.log
    if [ -f $InferenceTimingFile ]; then
        grep "Time taken by" "$InferenceTimingFile" | \
            cut -d $'\t' -f 2 | \
            xargs printf '%s\t'
    else
        printf '%s\t' "0"
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
    SOLUTIONSPrefix="Annotation: @"
    if [ -f $InferenceSolutionsFile ]; then
        for key in "${constantSlotsOutputKeys[@]}"; do
            # sift through the log files to find all the constant slot output values, sum them up and print it
            grep -w "$SOLUTIONSPrefix$key" "$InferenceSolutionsFile" | wc -l | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done

        grep "Annotation: @UnitsRep(" "$InferenceSolutionsFile" | wc -l | \
            awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
    else
        for key in "${constantSlotsOutputKeys[@]}"; do
            printf '%s\t' "0"
        done

        printf '%s\t' "0"
    fi

    INSERTKey=insert-annotation
    QUALPrefix=@units.qual.
    # printf "$JAIFFiles"
    if [ -f "$project/logs/infer_result_0.jaif" ]; then
        # echo "$JAIFFiles" | xargs printf '%s\t'

        count=$(grep -w "$INSERTKey" $project/logs/infer_result_*.jaif | wc -l)
        printf '%s\t' "$count"

        for key in "${insertedAnnotationKeys[@]}"; do
            grep -w "$INSERTKey.*$QUALPrefix$key" $project/logs/infer_result_*.jaif | wc -l | \
                awk -v tab="\t" '{sum += $1} END {printf sum+0 tab}'
        done
    else
        printf '%s\t' "0"
        for key in "${insertedAnnotationKeys[@]}"; do
            printf '%s\t' "0"
        done
    fi
    # insertedAnnotationKeys
    # infer_result_0.jaif

    printf '\n'
done
