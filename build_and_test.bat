@echo off

set JAVA_OPTS=-Djava.library.path="%CD%\dist\z3\bin"
set PATH=%CD%\dist\z3\bin

echo %PATH%
echo %JAVA_OPTS%

gradlew build
