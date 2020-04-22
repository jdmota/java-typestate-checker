# Mungo plugin for Checker Framework

## How it works

This version of Mungo is implemented as a plugin for the Checker Framework. Adding a `@MungoTypestate("ProtocolFile")` annotation to the top of a class enforces that instances of that class follow the protocol defined by the protocol file. Every time a method call on a object is encountered, we make sure that object is in a state that allows that invocation. The type of the object then changes to conform to the new state reached after that method call. We also make sure protocols are completed and that objects are used in a linear way.

### Type system

<!-- http://www.plantuml.com/plantuml/uml/SoWkIImgAStDuGhDoyxBByzJiAdHrLNmJyfAJIxXWb0G8R_y4jUybDGK5464249PG55-INvoFfg9VgKvQ281HPcvcIMPPQcemhxvPK0ZORP1n9poIqhoSxamHH2seGgNvg0AmEr24GLRXIBYa9gN0WmC0000 -->

![Type system](./type_system.svg)

- `Unknown` is the top type. It includes all possible values.
- `Object` contains all objects except `null`.
- `NotEnded` is the set of all objects with protocols that have not completed.
- `Ended` is the set of all objects with completed protocols.
- `NoProtocol` is the set of all objects without protocol.
- `Null` is the set with only the `null` value.
- `Primitive` is the set of all primitive values. Like integers and booleans.
- `Moved` is a type applied to variables that point to an object that was moved. Like in Rust, where if something takes ownership of some data, that data is considered to have been moved. Variables with the `Moved` type cannot be used, because they no longer own the data.
- `Bottom` is the bottom type. Used for computations that do not finish or error. Empty set. Like `Nothing` in many languages or like `never` in TypeScript.

Subtypes of `NotEnded` are for example, the type of files that are in the `Open` or `Read` states, or the type of files that are only in the `Open` state.

The type of files that are only in the `Open` state is also a subtype of the type of files that are in the `Open` or `Read` states, since the set `{Open}` is contained in `{Open, Read}`.

The type of files that are in the `Open` state and the type of files that are in the `Read` state are not subtypes of each other, since one is not contained in the other and vice-versa.

<!-- http://www.plantuml.com/plantuml/uml/SoWkIImgAStDuGhDoyxBByzJiAdHrLNmAyr15yalSSrBIKtXWZ4WmafkcJcfrVu5gNaw2a6fYIcrIboOGkXA2Ig2cWHo1KJOAR-a93-N2za850c4DZG9XzIy5A3l0000 -->

![Type system example](./type_system_example.svg)

#### Notes

1. `null` should NOT have the bottom type, otherwise its type would be the subtype of all types, allowing `null` assignments going unchecked. Which is what Java already (wrongly) does.
1. `Ended` and `Null` could be joined in an `Unusable` type. The reason to split both is to provide more information to error messages as to why an operation is not allowed.

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

## Build and test

- Unix: `./gradlew build`
- Windows: `gradlew.bat build`

## Build jar file

- Unix: `./gradlew buildJar`
- Windows: `gradlew.bat buildJar`

The produced jar file goes into the `examples` folder.

## Remote testing

- Unix: `./gradlew test --debug-jvm`
- Windows: `gradlew.bat test --debug-jvm`

## Running comparison tests

1. Extract [Checker Framework](https://checkerframework.org/) into the `examples` folder.
1. Build jar file.
1. Run:
    - Unix: TODO
    - Windows: `cd examples && run.bat`
1. Check `examples/comparison` and nested folders for results.

## Comparison

[Comparison table between this version of Mungo and other versions](https://github.com/jdmota/abcd-mungo/wiki/Comparison)

## Roadmap and TODO's

[Roadmap and TODO's](https://github.com/jdmota/abcd-mungo/wiki/Roadmap-and-TODOs)
