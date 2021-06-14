#!/bin/bash

CD=`pwd`

if [[ "$CD" =~ ^\/cygdrive.* ]]; then
	CD=`cygpath -w "$CD"`
fi

PATH="$PATH:$CD/../../dist/z3/bin"

java "-Djava.library.path=$CD/../../dist/z3/bin" -jar ../../dist/checker/checker.jar -classpath ../../dist/jatyc.jar -processor jatyc.JavaTypestateChecker LineReader.java Status.java Main2.java -AperformInference
