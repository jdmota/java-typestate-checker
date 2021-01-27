@echo off

set JAVA_OPTS=-Djava.library.path="%CD%\z3\bin"
set PATH=%PATH%;%CD%\z3\bin

echo %PATH%
echo %JAVA_OPTS%

java -jar checker-3.8.0/checker.jar -classpath jtc-checker.jar -processor org.checkerframework.checker.jtc.JavaTypestateChecker *.java

pause
