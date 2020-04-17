@ECHO OFF

TITLE Mungo Tests

:: java -jar ./mungo-73dd8ae.jar -cp ./mungo-73dd8ae.jar *.java

set originalMungo=../mungo-73dd8ae.jar

set checker=../checker-framework-3.1.1/checker/dist/checker.jar
set mungoChecker=../mungo-checker.jar
set mungoClass=org.checkerframework.checker.mungo.MungoChecker

FOR %%A IN (Adder) DO (
  cd %%A
  echo Running tests in %%A
  java -jar "%checker%" -classpath "%mungoChecker%" -processor %mungoClass% *.java
  cd ..
)

pause
