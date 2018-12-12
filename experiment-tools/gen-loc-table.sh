#!/bin/bash

if ! [ -n "$1" ]; then
    echo "This script gives the lines of code of a corpus"
    echo "usage: $0 <corpus-root-folder-name>"
    exit 1
fi

if ! [ -x "$(command -v cloc)" ]; then
  echo "Error: cloc is not installed. Run:" >&2
  echo "sudo apt install cloc" >&2
  exit 1
fi

cd $1

declare -a projects=($(ls -d */ | sort))

pad=$(printf '%0.1s' " "{1..60})
padlength=30

tab=$(printf '%s\t' "")

# Print header row
printf 'Project\tfiles\tlanguage\tblank\tcomment\tcode\n'

# Print each project
for project in "${projects[@]}"; do
    # print project name without trailing slash
    printf '%*.*s\t' 0 $((${#project} - 1)) "$project"

    result=$(cloc --quiet --csv --csv-delimiter="${tab}" --include-lang=Java ${project} | grep Java)
    printf '%s\n' "$result"
done

printf '\n'
