@echo off

set JAVA_OPTS=-Djava.library.path="%CD%\..\..\dist\z3\bin"
set PATH=%PATH%;%CD%\..\..\dist\z3\bin

java -jar ../../dist/checker/checker.jar -classpath ../../dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java -AperformInference

pause
