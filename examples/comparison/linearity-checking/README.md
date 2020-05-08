## Original Mungo's output

```

NotOk.java: 6-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 12-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 18-15: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 25-15: Semantic Error
		Object reference is used uninitialised.```

## Mungo Checker's output

```
NotOk.java:7: error: [Cannot call read on moved value] (Cannot call read on moved value)
    f.read();
          ^
NotOk.java:13: error: [argument.type.incompatible] incompatible types in argument.
    use(f);
        ^
  found   : Moved File
  required: FileProtocol{Read} File
NotOk.java:20: error: [Cannot call read on moved value] (Cannot call read on moved value)
    f.read();
          ^
NotOk.java:27: error: [argument.type.incompatible] incompatible types in argument.
    use(f);
        ^
  found   : Moved File
  required: FileProtocol{Read} File
NotOk.java:33: error: [f was moved to a different closure] (f was moved to a different closure)
      return f.read();
             ^
5 errors```
