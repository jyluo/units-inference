#!/bin/bash

folders=(src tests)


for folder in ${folders[@]}; do
	find ${folder} | grep java | xargs run-google-java-format.py
done
