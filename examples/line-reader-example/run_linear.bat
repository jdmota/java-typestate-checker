@echo off

java -jar ../../dist/checker-framework-3.8.0/checker/dist/checker.jar -classpath ../../dist/jtc-checker.jar -processor org.checkerframework.checker.jtc.JavaTypestateChecker LineReader.java Status.java Main1.java

pause
