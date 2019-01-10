#!/bin/bash

# Readme: http://openjdk.java.net/projects/code-tools/jmh/

mvn clean install

java -jar target/benchmarks.jar
