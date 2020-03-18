## TODO's

- Create more tests
- Document tests (latex)
  - Code and output

### Features

- @MungoState({})
- Support state change depending on exceptions
- Inheritance? Protocols in interfaces?
  - What if a class has a protocol, and implements an interface with a protocol as well?
  - Test if a protocol is a subtype of other protocol? How so?

### Important things to test/fix

- Objects with no protocol are getting the unknown type, disallowing any use of them
- Should "end" be in the list of concrete states? If not, depends on:
  - Control that if an object reaches the "end" state, it is dropped
- Force an object to reach the "end" state if dropped
- Deal with the values of fields inside objects
  - Combating against defensive programming
- Validate protocols
  - Check if there are duplicate transitions, if types exist, etc...
- Review other todo's in the code...

## Proposals from thesis plan

- [x] Replacing the mungo.lib.Boolean enumeration with the standard boolean
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
