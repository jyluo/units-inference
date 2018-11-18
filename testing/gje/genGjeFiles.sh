#!/bin/bash

../../run-units-infer.sh gauss ExactConstrained.java
mv gjeConstraints_m.gje sampleFiles/exact.gje

../../run-units-infer.sh gauss OverSpecified.java
mv gjeConstraints_m.gje sampleFiles/overspec.gje

../../run-units-infer.sh gauss UnderConstrained.java
mv gjeConstraints_m.gje sampleFiles/under.gje

../../run-units-infer.sh gauss Unsat.java
mv gjeConstraints_m.gje sampleFiles/unsat.gje

../../run-units-infer.sh gauss ExactConstrained.java OverSpecified.java UnderConstrained.java
mv gjeConstraints_m.gje sampleFiles/mixSat.gje

../../run-units-infer.sh gauss ExactConstrained.java OverSpecified.java UnderConstrained.java Unsat.java
mv gjeConstraints_m.gje sampleFiles/mixUnsat.gje

rm *.gje
rm *.txt
rm *.class
