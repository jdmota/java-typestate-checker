@echo off

set JAVA_OPTS=-Djava.library.path="C:/Users/JOTA/Desktop/GitHub/abcd-mungo/z3/bin"
set PATH=C:/Users/JOTA/Desktop/GitHub/abcd-mungo/z3/bin

echo %PATH%
echo %JAVA_OPTS%

gradlew build
