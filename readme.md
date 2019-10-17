# Mungo

This is a front-end tool used to statically check the order of method calls. It is implemented using the [JastAdd](http://jastadd.org/web/) framework and [ExtendJ](https://extendj.org/index.html) compiler.

A typestate, or protocol file( .protocol) is defined and associated to a class, through an annotation. A protocol definition is described as a sequence of method calls, the order of which determines the validity of the protocol. The Mungo tool checks that the object instantiating the class performs method calls by following its declared typestate. If the typestate is violated, Mungo reports the errors.

## Cloning this Project

To clone this project you will need [Git](https://git-scm.com) installed.

Use this command to clone the project with Git:

    git clone --recursive <REPOSITORY URL>

The `--recursive` flag makes Git also clone the ExtendJ submodule while cloning the mungo repository.

## Build and Run

This project is built with [Gradle](https://gradle.org), but you do not need to install Gradle to use it. If you have Java installed, run the following commands to build the project:


    ./gradlew jar

If you are running on Windows, replace ./gradlew by just gradlew.

**How to run:**



		java -jar mungo.jar

gives you a description of the usage of the mungo typechecker.


		java -jar mungo.jar -classpath .:mungo.jar [options] [FILES]

performs type check on the files specified by FILES with the options specified by [options]

**Examples:**


Collection examples


	java -jar mungo.jar -classpath .:mungo.jar examples/collection/Stack.java


    java -jar mungo.jar -classpath .:mungo.jar examples/collection/StackUser/StackUser.java


    java -jar mungo.jar -classpath .:mungo.jar examples/collection/StackUser2/StackUser.java

The other examples can be run in a similar fashion.

If no errors are detected the program can be compiled and run using `javac`,
like any other Java program.

**To import the typestate annotation mungo.jar should be added as an external library.**
