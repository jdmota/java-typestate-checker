## Mungo Checker's output

```
NotOk.java:8: error: [Cannot override because object has not ended its protocol] (Cannot override because object has not ended its protocol)
        f = null;
        ^
NotOk.java:9: error: [Cannot call close on null] (Cannot call close on null)
        f.close();
               ^
NotOk.java:17: error: [argument.type.incompatible] incompatible types in argument.
    use(null);
        ^
  found   : Null null
  required: FileProtocol{Init|Read|Close} File
NotOk.java:20: error: [Object did not complete its protocol. Type: FileProtocol{Init|Read|Close}] (Object did not complete its protocol. Type: FileProtocol{Init|Read|Close})
  public static void use(File f) {
                              ^
4 errors
```

## Original Mungo's output

```

NotOk.java: 8-13: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 3. Typestate mismatch. Found: end. Expected: void close().

Ok.java: 5-25: Semantic Error
		Object reference is used uninitialised.
```
