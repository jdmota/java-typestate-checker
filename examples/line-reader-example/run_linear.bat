@echo off

java -jar ../../dist/checker/checker.jar -classpath ../../dist/jatyc.jar -processor jatyc.JavaTypestateChecker LineReader.java Status.java Main1.java

pause
