@ECHO OFF

TITLE Mungo Tests

set examplesDir=%CD%

set originalMungo=%CD%/mungo-73dd8ae.jar

set mungoChecker=%CD%/mungo-checker.jar
set mungoCheckerLib=%CD%/mungo-checker-lib.jar
set mungoCheckerClass=org.checkerframework.checker.mungo.MungoChecker

set checkerVersion=3.3.0
set checker=%CD%/checker-framework-%checkerVersion%/checker/dist/checker.jar

if not exist %checker% (
  echo Comparison tests depend on the Checker Framework
  echo Did not find file %checker%
  exit /b 1
)

FOR %%F IN (
  comparison/basic-checking
  comparison/boolean-decision
  comparison/nullness-checking
  comparison/file-1
  comparison/iterator-attempt1
  comparison/iterator-attempt2
  comparison/iterator-attempt3
  comparison/iterator-attempt4
  comparison/iterator-attempt5
  comparison/iterator-attempt6
  comparison/iterator-attempt7
  comparison/original-mungo-continue-issue
) DO (
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
    java -jar "%originalMungo%" -classpath "%originalMungo%;%mungoCheckerLib%" *.java
    echo ```
  ) > README.md 2>&1
  cd %examplesDir%
)
