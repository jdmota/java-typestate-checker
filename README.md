# Java Typestate Checker

[Changelog](https://github.com/jdmota/java-typestate-checker/wiki/Changelog) | [Documentation](https://github.com/jdmota/java-typestate-checker/wiki/Documentation)

The Java Typestate Checker is a plugin for the Checker Framework. This plugin allows one to statically ensure that method calls are called in the correct order. The sequences of method calls allowed are specified in a protocol file which is associated with a Java class by adding a `@Typestate` annotation to the class. This tool was inspired in the [Mungo tool](http://www.dcs.gla.ac.uk/research/mungo/index.html). It is a new implementation which includes new features and improvements over the current version of Mungo. A comparison table between Mungo and this tool is available [here](https://github.com/jdmota/abcd-mungo/wiki/Comparison).

## Features

**Latest feature: initial support for subtyping!**

- checking that **methods are called in the correct order** specified by the protocol;
- checking that **protocols of objects are completed**;
- checking the **absence of null pointer errors**;
- a **language of assertions** that focuses in allowing a program that uses typestates to be type-checked even in the presence of aliasing;
- an **inference algorithm** which analyzes the code statically and infers all the required assertions;
- support for **protocols to be associated with classes** from the standard Java library or from third-party libraries;
- support for **"droppable" states**, which allow one to specify states in which an object may be "dropped" (i.e. stop being used) without having to reach the final state;
- support for **transitions of state to depend on boolean values or enumeration values** returned by methods.
- invalid sequences of method calls are ignored when analyzing the use of objects stored inside other objects by taking into account that the methods of the outer object will only be called in the order specified by the corresponding protocol, thus **avoiding false positives**.

The tool has two modes:

- Linear mode: where objects must be used linearly;
- Non-linear mode: where objects may be aliased (this mode uses the **language of assertions** and the **inference algorithm**). It is highly experimental, including several limitations, and may not provide the same guarantees that the linear mode is able to provide.

## Subtyping

The latest version adds support for subtyping: you may have a class with a protocol that extends another class with another protocol and the tool will ensure that the first protocol is a subtype of the second protocol.

One can also create a class with protocol that extends a class without protocol. In the class without protocol, all methods are available to be called and remain so in the subclass. Then in the subclass, one can add new methods and restrict their use by only allowing them in certain states.

If a class extends another class with protocol, but does not include a `@Typestate` annotation, the subclass assumes by default the same protocol of its superclass.

In Java, up and down-casts may occur explicitly and up-casts may occur implicitly when assigning to local variables or fields, passing objects to parameters or returning objects. With this initial support for subtyping, up and down casting is only allowed between initial states or final states.

You may find more information in the [documentation page](https://github.com/jdmota/java-typestate-checker/wiki/Documentation).

## Quick Start

1. Make sure you have JDK 8 installed. We recommend the [OpenJDK distribution](https://adoptopenjdk.net/?variant=openjdk8&jvmVariant=hotspot).
1. Run the following commands:

```sh
git clone https://github.com/jdmota/java-typestate-checker.git
cd java-typestate-checker/examples/quick-start
java -jar ../../dist/checker/checker.jar -classpath ../../dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java
```

You should get the following output:

```
Main.java:7: error: Cannot call [next] on State{JavaIterator, end}
      iterator.next();
                   ^
Main.java:2: error: [iterator] did not complete its protocol (found: State{JavaIterator, Next})
  public static void main(String[] args) {
                     ^
2 errors
```

## Installation

1. Make sure you have JDK 8 installed. We recommend the [OpenJDK distribution](https://adoptopenjdk.net/?variant=openjdk8&jvmVariant=hotspot).
1. Clone this repository: `git clone https://github.com/jdmota/java-typestate-checker.git`
1. Run the following command from the folder where the Java files you want to check are by replacing `REPO` with the appropriate path to the repository cloned in step 2.

```sh
java -jar REPO/dist/checker/checker.jar -classpath REPO/dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java
```

Optional: To use the experimental non-linear mode, make sure the environment variable `PATH` includes `REPO/dist/z3/bin` and then run the following command instead:

```sh
java -Djava.library.path=REPO/dist/z3/bin -jar REPO/dist/checker/checker.jar -classpath REPO/dist/jatyc.jar -processor jatyc.JavaTypestateChecker *.java -AperformInference
```

<!--## Demo

You can find an example with instructions on how to experiment with the tool in the folder [examples/line-reader-example](./examples/line-reader-example).

You may also find other examples in the [examples folder](./examples).-->

## Resources

- [Examples](./examples)
- [Tutorial](https://youtu.be/_zrcqYPe8-8)
- [Paper](./docs/jatyc-paper.pdf)
- [Master Thesis](./docs/msc-thesis.pdf)

<!-- http://www.plantuml.com/plantuml/uml/NSqn2i9048NXVayHKgcG6rW4mT8O40yGirEixix0-YOs7bx8Wc6sUl0Lx-_Vc38qHNVd5yk7c-EtwvhhuqapN9b2xGqJQ7VOjuRFxCaR6MJC0fcb-XmqLZBca0B2GfOlif1tMw_eIG19RkqPsNgMDLhuruokCICziTSKVm00 -->

<!-- http://www.plantuml.com/plantuml/uml/SoWkIImgAStDuGhDoyxBByzJiAdHrLNmAyr14r4ABaaiITNGqbJYGZ2XKcwPEQdL_WMfUJeAGQc9ARLAN1X264e9AeAQ1789HDWflwGaFvSBsGWK2OGsD0c7rBmKe0y1 -->

<!--

### Type system

![Type system](./type_system.svg)

- `Unknown` is the top type. It includes all possible values.
- `Object` contains all objects except `null`.
- `State` represents objects which are in a specific state.
- `Ended` is the set of all objects with completed protocols.
- `NoProtocol` is the set of all objects without protocol.
- `Null` is the set with only the `null` value.
- `Primitive` is the set of all primitive values. Like integers and booleans.
- `Moved` is a type applied to variables that point to an object that was moved. Like in Rust, where if something takes ownership of some data, that data is considered to have been moved. Variables with the `Moved` type cannot be used, because they no longer own the data.
- `Bottom` is the bottom type. Used for computations that do not finish or error. Empty set. Like `Nothing` in many languages or like `never` in TypeScript.

Subtypes of `State(*)` are for example, the type of files that are in the `Open` or `Read` states, or the type of files that are only in the `Open` state.

The type of files that are only in the `Open` state is also a subtype of the type of files that are in the `Open` or `Read` states, since the set `{Open}` is contained in `{Open, Read}`.

The type of files that are in the `Open` state and the type of files that are in the `Read` state are not subtypes of each other, since one is not contained in the other and vice-versa.

![Type system example](./type_system_example.svg)

### Checking

- The type checker tracks all the possible states that an object might be in.
- When initializing, an object is only in its initial state.
- If a variable declaration is encountered, for example in a method argument, it is assumed that the object might be in any of its states. That can be refined with the use of `@MungoState({"Open"})`.
- When a method invocation is encountered, considering all possible states, the type checker creates a set with all the possible destination states via that method invocation. If that method invocation happened on the condition of a `if/while` statement or in the expression of a `switch` statement, the possible states are properly refined: if the transition leads to a decision state, only the destination state associated with the relevant label is added to the set of possible states.

### Architecture

Plugins for the Checker Framework usually extend the `BaseTypeChecker` and then override some aspects of it if necessary. To understand how plugins work it is important to understand how information is stored:

- [AnnotatedTypeMirror](https://checkerframework.org/api/org/checkerframework/framework/type/AnnotatedTypeMirror.html)'s represent types and store type annotations associated with the type. Those annotations constitute the type information specific to the type system implemented by a plugin.
- [Tree](https://docs.oracle.com/en/java/javase/11/docs/api/jdk.compiler/com/sun/source/tree/Tree.html?is-external=true)'s are nodes in an abstract syntax tree.
- [Element](https://docs.oracle.com/en/java/javase/11/docs/api/java.compiler/javax/lang/model/element/Element.html?is-external=true)'s represent a potentially-public declaration that can be accessed from elsewhere: classes, interfaces, methods, constructors, and fields.

Our plugin is composed by:

- `MungoChecker`: The plugin's entry point.
- `MungoVisitor`: Performs assignment checking, method invocation checking and other checks.
- `MungoAnnotatedTypeFactory`: Applies annotations via `MungoDefaultQualifierForUseTypeAnnotator` and `MungoTreeAnnotator`, which are refined by the flow-sensitive analysis provided by `MungoAnalysis` and `MungoTransfer`
- `MungoQualifierHierarchy`: Defines the subtyping relationship between annotations
- `MungoDefaultQualifierForUseTypeAnnotator`: Applies a set of annotations to [Elements](https://docs.oracle.com/en/java/javase/11/docs/api/java.compiler/javax/lang/model/element/Element.html?is-external=true)
- `MungoTreeAnnotator`: Applies a set of annotations to [Trees](https://docs.oracle.com/en/java/javase/11/docs/api/jdk.compiler/com/sun/source/tree/Tree.html?is-external=true)
- `MungoAnalysis`: Tracks annotations using flow-sensitive analysis
- `MungoTransfer`: Applies type information refinement

Since annotations are only able to store some types of values, not arbitrary objects, we store a `long` id value in each annotation that is then mapped to an object which stores the concrete type information.

More details: [Manual - How to create a Checker plugin](https://checkerframework.org/manual/#creating-a-checker)
-->

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

### Running comparison tests

1. Build jar file.
1. Run `cd examples && bash run` on Unix or Cygwin.
1. Check `examples/comparison` and nested folders for results.
