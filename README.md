# Mungo plugin for Checker Framework

## How it works

This version of Mungo is implemented as a plugin for the Checker Framework. Adding a `@MungoTypestate("ProtocolFile")` annotation to the top of a class enforces that instances of that class follow the protocol defined by the protocol file. Every time a method call on a object is encountered, we make sure that object is in a state that allows that invocation. The type of the object then changes to conform to the new state reached after that method call. We also make sure protocols are completed and that objects are used in a linear way.

### Type system

<!-- http://www.plantuml.com/plantuml/uml/SoWkIImgAStDuGhDoyxBByzJiAdHrLNmooznpKj9JK4L1GkXAmmeoY_9Jyv7Dw0q1qt4DxyCg1bcC4JCAR-a93-N2rC4OIogS6aEgW3OK1GHXzIy5A1t0000 -->

![Type system](./type_system.svg)

- `Unknown` is the top type. It includes all possible values.
- `NotEnded` is the set of all objects with protocols that have not completed.
- `Ended` is the set of all objects with completed protocols.
- `NoProtocol` is the set of all objects without protocol.
- `Null` is the set with only the `null` value.
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

## Building

- Unix: `./gradlew build`
- Windows: `gradlew.bat build`

## Remote testing

- Unix: `./gradlew test --debug-jvm`
- Windows: `gradlew.bat test --debug-jvm`

## Roadmap

- Version 1.0
    - Equal to Mungo (Glasgow implementation + SCP paper)
    - With protocol completeness and without null pointer exceptions
        - References: Aalborg Haskell implementation + new tech report
    - With examples to argue for correctness
- Version 2.0
    - Finer ownership control than linearity
- Version 3.0
    - Collections with typestate control of its values
    - Generics support

## TODO's

### General

- Update this README with further information
- Create more tests
- Document tests (latex)
  - Code and output
- Review other todo's in the code

### Version 1.0

- [x] `@MungoState({"HasNext"})`
    - [x] Basic implementation
        - Commit [dc5393](https://github.com/jdmota/abcd-mungo/commit/dc5393e67bc1608da71e4549676970b9166a6994).
    - [x] Check method arguments - e.g. `use(@MungoState({"Next"}) Iterator it)`
        - Commit [f3502a](https://github.com/jdmota/abcd-mungo/commit/f3502ae38da23cf3507557e67fac94d03d309175)
    - [x] Check variable declarations - e.g. `@MungoState({}) Iterator it = etc;`
        - Commit [4d646b](https://github.com/jdmota/abcd-mungo/commit/4d646b3b894e545a9bd3611cd5616fc29acc24cc).
- [ ] `@MungoNull`
- [x] Objects with no protocol are getting the unknown type, disallowing any use of them
    - Solution: Create a type for objects with no protocols instead of attributing them the `Unknown` type.
    - Commit [b86fad](https://github.com/jdmota/abcd-mungo/commit/b86fadd117e6fb2044cad2325bce7d2386d80148). [Relevant changes](https://github.com/jdmota/abcd-mungo/commit/b86fadd117e6fb2044cad2325bce7d2386d80148#diff-73b7b3bab8528295364734fe900cbd6f).
- [x] When the states are unknown, all possible ones are being attributed, including final ones
    - Solution: Create "EndedType" distinguishing from normal states
    - Commit [b86fad](https://github.com/jdmota/abcd-mungo/commit/b86fadd117e6fb2044cad2325bce7d2386d80148). [Relevant changes](https://github.com/jdmota/abcd-mungo/commit/b86fadd117e6fb2044cad2325bce7d2386d80148#diff-f6e3068f239b50fb479594bf289764e7).
- [ ] Force linear use of objects with protocol
    - [x] Basic implementation
        - Commit [8f39c4](https://github.com/jdmota/abcd-mungo/commit/8f39c407e7acb7c7e48739ebc47e32565c2cd387).
    - [x] Upon return, refine the type to "moved"
        - Commit [6c94a7](https://github.com/jdmota/abcd-mungo/commit/6c94a74c99e1ac4a3c6a685f581339c4f5b33368).
    - [ ] Fix corner cases (leaked `this`, moving to a different closure)
- [x] Force object protocol to complete
    - [x] Only allow null assignments if object is in the end state or is already null
        - Commit [67dca7](https://github.com/jdmota/abcd-mungo/commit/67dca7cce7a9e36178ce77a933139fc4a1612093).
    - [x] Only allow variable override if object is in the end state or is already null
        - Commit [8e297e](https://github.com/jdmota/abcd-mungo/commit/8e297ebf6d892e46f0d5a95ff27cf861b7aa88bc).
    - [x] Check the end of a method to see if the object was moved, is null, or reached the end state
        - Commit [9a3762](https://github.com/jdmota/abcd-mungo/commit/9a3762eaedd289d3171010d3383c4e5b6ee813e1).
    - [x] Check the end of any block to see if the object was moved, is null, or reached the end state
        - Commit [1bbc77](https://github.com/jdmota/abcd-mungo/commit/1bbc778ef75c9c87acdce73398a21d33af52646e).
    - [x] Check that if a method returns an object with a non-ended protocol, that object is used
        - Commit [6c94a7](https://github.com/jdmota/abcd-mungo/commit/6c94a74c99e1ac4a3c6a685f581339c4f5b33368).
- [ ] Analyze fields inside objects (combating against defensive programming)
- [ ] Validate protocols: check if there are duplicate transitions, if types exist, etc...
- [ ] Understand why Checker is reporting more errors than necessary

### Version 2.0

- [ ] Relax linear use of objects with protocol
    - [ ] Implement some type of ownership/borrowing system like Rust?
    - [ ] Fix corner cases (objects in collections: do not allow collections to have ownership of ended objects)

### Version 3.0

- [ ] Collections support
- [ ] Generics support

## Proposals from thesis plan

- [x] Replacing the mungo.lib.Boolean enumeration with the standard boolean
    - Out of the box with Checker
- [x] Improving of flow analysis around loops and switch statements
    - Out of the box with Checker
- [ ] Recognition of decisions made with if statements
- [ ] Ability to associate protocol definitions with already present classes or interfaces
- [ ] Adding support for droppable objects
- [ ] Generics
- [ ] Collections support
    - Done in part: if a method is available in all states, its call is allowed.
    - This allows one to check the current state of an object.
- [ ] Adding support for state transitions depending on method arguments

### Other features

- [ ] Support state change depending on exceptions
- [ ] Inheritance? Protocols in interfaces?
    - What if a class has a protocol, and implements an interface with a protocol as well?
    - Test if a protocol is a subtype of other protocol? How so?
