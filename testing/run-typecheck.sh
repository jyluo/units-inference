#!/bin/bash

# has to be executed from ~/jsr308/units-inference/bin because classpath isn't being properly handled
cd ../bin
../run-units-typecheck.sh ../testing/Test.java
