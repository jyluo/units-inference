#!/bin/bash
if ! [ -n "$1" ]; then
    echo "This script converts an unsat output into a dot graph definition."
    echo "usage: $0 unsatConstraints.txt"
    exit 1
fi

FILENAME=$1

# digraph G {
#   "Welcome" -> "To"
#   "To" -> "Web"
#   "To" -> "GraphViz!"
# }

echo ""

echo "digraph G {
  rankdir=LR;
  node[
    shape = none,
    margin = 0.05,
    width = 0,
    height = 0,
    color = lightgray,
    style = filled,
    fontname = \"Helvetica-Outline\",
    fontsize = 10];"

grep "<:" $FILENAME | \
  sed -r 's/[ ]*([0-9]+[a-zA-Z0-9 @]*) <: ([0-9]+[a-zA-Z0-9 @]*)$/  "\2" -> "\1"/p' \
  | sort | uniq

grep " == " $FILENAME | \
  sed -r 's/[ ]*([0-9]+[a-zA-Z0-9 @]*) == ([0-9]+[a-zA-Z0-9 @]*)$/  "\2" -> "\1" [arrowhead=none]/p' \
  | sort | uniq

echo "}"

echo ""

echo "// copy and paste to http://www.webgraphviz.com/"
