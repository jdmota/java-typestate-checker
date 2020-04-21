@ECHO OFF

TITLE Mungo Tests

set examplesDir=%CD%

set originalMungo=%CD%/mungo-73dd8ae.jar

set mungoChecker=%CD%/mungo-checker.jar
set mungoCheckerClass=org.checkerframework.checker.mungo.MungoChecker

set checkerVersion=3.3.0
set checker=%CD%/checker-framework-%checkerVersion%/checker/dist/checker.jar

if not exist %checker% (
  echo Comparison tests depend on the Checker Framework
  echo Did not find file %checker%
  exit /b 1
)

FOR %%F IN (comparison/file-1) DO (
  cd %%F
  echo Running tests in "%%F"
  (
    echo ## Mungo Checker's output
    echo.
    echo ```
    java -jar "%checker%" -classpath "%mungoChecker%" -processor %mungoCheckerClass% *.java
    echo ```
    echo.
    echo ## Original Mungo's output
    echo.
    echo ```
    java -jar "%originalMungo%" -classpath "%originalMungo%" *.java
    echo ```
  ) > README.md 2>&1
  cd %examplesDir%
)
