@echo off

java -jar checker-3.8.0/checker.jar -classpath jtc-checker.jar -processor org.checkerframework.checker.jtc.JavaTypestateChecker *.java

pause
