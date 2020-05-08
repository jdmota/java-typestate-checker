## Original Mungo's output

```

NotOk.java: 10-13: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 5. Typestate mismatch. Found: end. Expected: void close().

Ok.java: 6-25: Semantic Error
		Object reference is used uninitialised.```

## Mungo Checker's output

```
NotOk.java:10: error: [Cannot override because object has not ended its protocol] (Cannot override because object has not ended its protocol)
        f = null;
        ^
NotOk.java:11: error: [Cannot call close on null] (Cannot call close on null)
        f.close();
               ^
NotOk.java:19: error: [argument.type.incompatible] incompatible types in argument.
    use(null);
        ^
  found   : Null null
  required: FileProtocol{Init} File
3 errors```
