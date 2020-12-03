## Mungo's output

```

NotOk.java: 5-14: Semantic Error
		Object created at NotOk.java: 5. Typestate mismatch. Found: end. Expected: String read(), void close().

NotOk.java: 9-14: Semantic Error
		Object created at NotOk.java: 9. Typestate mismatch. Found: end. Expected: String read(), void close().```

## Our tool's output

```
NotOk.java:5: error: [Object did not complete its protocol. Type: State "Read"] (Object did not complete its protocol. Type: State "Read")
    File f = new File();
         ^
NotOk.java:13: error: [Object did not complete its protocol. Type: State "Read"] (Object did not complete its protocol. Type: State "Read")
  public static void use(File f) {
                              ^
2 errors```
