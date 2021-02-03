@echo off

set JAVA_OPTS=-Djava.library.path="%CD%\..\..\dist\z3\bin"
set PATH=%PATH%;%CD%\..\..\dist\z3\bin

java -jar ../../dist/checker-framework-3.8.0/checker/dist/checker.jar -classpath ../../dist/jtc-checker.jar -processor org.checkerframework.checker.jtc.JavaTypestateChecker *.java -AperformInference

pause
