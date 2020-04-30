## Original Mungo's output

```

NotOk.java: 7-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 13-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 19-15: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 26-15: Semantic Error
		Object reference is used uninitialised.```

## Mungo Checker's output

```
NotOk.java:8: error: [Cannot call read on moved value] (Cannot call read on moved value)
    f.read();
          ^
NotOk.java:14: error: [argument.type.incompatible] incompatible types in argument.
    use(f);
        ^
  found   : Moved File
  required: FileProtocol{Read} File
NotOk.java:21: error: [Cannot call read on moved value] (Cannot call read on moved value)
    f.read();
          ^
NotOk.java:28: error: [argument.type.incompatible] incompatible types in argument.
    use(f);
        ^
  found   : Moved File
  required: FileProtocol{Read} File
NotOk.java:34: error: [f was moved to a different closure] (f was moved to a different closure)
      return f.read();
             ^
5 errors```
