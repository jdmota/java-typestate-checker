@echo off

java -jar ../../dist/checker/checker.jar -classpath ../../dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java
