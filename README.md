# Java Typestate Checker

[Quick Start](#quick-start) | [Installation](#installation) | [Resources](#resources) | [Publications](#publications) | [Changelog](https://github.com/jdmota/java-typestate-checker/wiki/Changelog) | [Documentation](https://github.com/jdmota/java-typestate-checker/wiki/Documentation)

The **Java Typestate Checker (JaTyC)** is a tool that verifies Java source code with respect to typestates. A typestate is associated with a Java class with the `@Typestate` annotation and defines: the object's states, the methods that can be safely called in each state, and the states resulting from the calls. The tool statically verifies that when a Java program runs: sequences of method calls obey to object's protocols; objects' protocols are completed; null-pointer exceptions are not raised; subclasses' instances respect the protocol of their superclasses.

**JaTyC** is a plugin for the [Checker Framework](https://checkerframework.org/). It is a purely transparent checker, i.e. does not modify the baseline Java compilation. This tool was inspired in the [Mungo toolset](http://www.dcs.gla.ac.uk/research/mungo/index.html). It is a new implementation which includes new features and improvements over the current version of Mungo. A comparison table between Mungo and this tool is available [here](https://github.com/jdmota/java-typestate-checker/wiki/Mungo-comparison).

## Features

**Latest feature: support for subtyping!**

- checking that **methods are called in the correct order** specified by the protocol;
- checking that **protocols of objects are completed**;
- checking the **absence of null pointer errors**;
- support for **protocols to be associated with classes** from the standard Java library or from third-party libraries;
- support for **"droppable" states**, which allow one to specify states in which an object may be "dropped" (i.e. stop being used) without having to reach the final state;
- support for **transitions of state to depend on boolean values or enumeration values** returned by methods.
- invalid sequences of method calls are ignored when analyzing the use of objects stored inside other objects by taking into account that the methods of the outer object will only be called in the order specified by the corresponding protocol, thus **avoiding false positives**.

_Note: if you are looking for the experimental non-linear mode (where objects may be aliased), check out the [non-linear-mode branch](https://github.com/jdmota/java-typestate-checker/tree/non-linear-mode)._

## Subtyping

The latest version adds support for subtyping: you may have a class with a protocol that extends another class with another protocol and the tool will ensure that the first protocol is a subtype of the second protocol.

One can also create a class with protocol that extends a class without protocol. In the class without protocol, all methods are available to be called and remain so in the subclass. Then in the subclass, one can add new methods and restrict their use by only allowing them in certain states.

If a class extends another class with protocol, but does not include a `@Typestate` annotation, the subclass assumes by default the same protocol of its superclass.

In Java, up and down-casts may occur explicitly and up-casts may occur implicitly when assigning to local variables or fields, passing objects to parameters or returning objects.

You may find more information in the [documentation page](https://github.com/jdmota/java-typestate-checker/wiki/Documentation).

## Quick Start

1. Make sure you have JDK 11 installed. Other versions might work but were not tested. We recommend [Eclipse Temurin](https://adoptium.net/temurin/releases/?version=11).
1. Run the following commands:

```sh
git clone https://github.com/jdmota/java-typestate-checker.git
cd java-typestate-checker/examples/quick-start
java -jar ../../dist/checker/checker.jar -classpath ../../dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java
```

You should get the following output:

```
Main.java:2: error: [iterator] did not complete its protocol (found: State{JavaIterator, Next})
  public static void main(String[] args) {
                     ^
Main.java:6: error: Cannot call [next] on State{JavaIterator, end}
      iterator.next();
                   ^
2 errors
```

## Installation

### Via Git

1. Make sure you have JDK 11 installed. Other versions might work but were not tested. We recommend [Eclipse Temurin](https://adoptium.net/temurin/releases/?version=11).
1. Clone this repository: `git clone https://github.com/jdmota/java-typestate-checker.git`
1. Run the following command from the folder where your source Java files are. Replace `REPO` with the appropriate path to the repository cloned in step 2.

```sh
java -jar REPO/dist/checker/checker.jar -classpath REPO/dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java
```

### Manual

1. Make sure you have JDK 11 installed. Other versions might work but were not tested. We recommend [Eclipse Temurin](https://adoptium.net/temurin/releases/?version=11).
1. Download and extract [checker-framework-3.28.0.zip](https://github.com/typetools/checker-framework/releases/tag/checker-framework-3.28.0).
1. Download [jatyc.jar](https://github.com/jdmota/java-typestate-checker/raw/master/dist/jatyc.jar).
1. Run the following command from the folder where your source Java files are. Replace `DOWNLOADS` with the appropriate path containing the files downloaded in steps 2 and 3.

```sh
java -jar DOWNLOADS/checker-framework-3.28.0/checker/dist/checker.jar -classpath DOWNLOADS/jatyc.jar -processor jatyc.JavaTypestateChecker *.java
```

## Resources

- [Examples](./examples)
- [Tutorial](https://youtu.be/_zrcqYPe8-8)

## Publications

- [A Java typestate checker supporting inheritance](https://www.sciencedirect.com/science/article/pii/S0167642322000776). Lorenzo Bacchiani, Mario Bravetti, Marco Giunti, João Mota, António Ravara. Science of Computer Programming 2022. ([pdf](./docs/a-java-typestate-checker-supporting-inheritance.pdf))
- [Java Typestate Checker](https://link.springer.com/chapter/10.1007/978-3-030-78142-2_8). João Mota, Marco Giunti, António Ravara. COORDINATION 2021. ([pdf](./docs/jatyc-paper.pdf))
- Coping with the reality: adding crucial features to a typestate-oriented language. João Mota. Master Thesis 2021. ([pdf](./docs/msc-thesis.pdf))

## Developer information

### Build and test

- Unix: `./gradlew build`
- Windows: `gradlew.bat build`

### Build jar file

- Unix: `./gradlew buildJar`
- Windows: `gradlew.bat buildJar`

The produced jar file goes into the `dist` folder.

### Remote testing

- Unix: `./gradlew test --debug-jvm`
- Windows: `gradlew.bat test --debug-jvm`
