#!/bin/bash

WORKING_DIR=$(cd $(dirname "$0") && pwd)
UI=$WORKING_DIR/..

count=$(grep -w "@BaseUnit" $UI/src/units/qual/*.java | wc -l)
echo "Num of Base Units In System: $count"
grep -l "@BaseUnit" $UI/src/units/qual/*.java | rev | cut -d '/' -f 1 | rev
