#!/bin/bash

export PATH="/usr/local/opt/openjdk@11/bin:$PATH" &&
java -jar ../../dist/checker/checker.jar -classpath ../../dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java
