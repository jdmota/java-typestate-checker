#!/bin/bash
javac -cp "jedis/lib/*:../../dist/checker/checker.jar:../../dist/jatyc.jar" -processor jatyc.JavaTypestateChecker -d out $(find jedis/src/main/java -name "*.java") JedisBug.java
