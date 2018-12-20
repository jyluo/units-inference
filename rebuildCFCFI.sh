#!/bin/bash

echo "Rebuilding CF"
(cd $CF; gradle assemble jar)

echo "Rebuilding CFI"
(cd $CFI; gradle dist jar dependenciesJar)
