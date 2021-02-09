#!/bin/bash

CD=`pwd`

if [[ "$CD" =~ ^\/cygdrive.* ]]; then
	CD=`cygpath -w "$CD"`
fi

PATH="$PATH:$CD/../../dist/z3/bin"

java "-Djava.library.path=$CD/../../dist/z3/bin" -jar ../../dist/checker-framework-3.8.0/checker/dist/checker.jar -classpath ../../dist/jtc-checker.jar -processor org.checkerframework.checker.jtc.JavaTypestateChecker LineReader.java Status.java Main2.java -AperformInference
