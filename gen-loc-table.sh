#!/bin/bash

cd ./$1

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

tab=$(printf '%s\t' "")

# Print header row
printf 'Project\tfiles\tlanguage\tblank\tcomment\tcode\t'
for key in "${statsKeys[@]}"; do
    printf '%s\t' "$key"
done
printf '\n'

# Print each project
for project in "${projects[@]}"; do
    # print project name without trailing slash
    printf '%*.*s\t' 0 $((${#project} - 1)) "$project"

    cloc --quiet --csv --csv-delimiter="${tab}" --include-lang=Java ${project} | grep Java
done

printf '\n'
