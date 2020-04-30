## Original Mungo's output

```

NotOk.java: 6-14: Semantic Error
		Object created at NotOk.java: 6. Typestate mismatch. Found: end. Expected: String read(), void close().

NotOk.java: 10-14: Semantic Error
		Object created at NotOk.java: 10. Typestate mismatch. Found: end. Expected: String read(), void close().

NotOk.java: 15-14: Semantic Error
		Object created at NotOk.java: 15. Typestate mismatch. Found: end. Expected: String read(), void close().

NotOk.java: 20-14: Semantic Error
		Object created at NotOk.java: 20. Typestate mismatch. Found: end. Expected: String read(), void close().```

## Mungo Checker's output

```
NotOk.java:6: error: [Object did not complete its protocol. Type: FileProtocol{Read}] (Object did not complete its protocol. Type: FileProtocol{Read})
    File f = new File();
         ^
NotOk.java:20: error: [Object did not complete its protocol. Type: FileProtocol{Read}] (Object did not complete its protocol. Type: FileProtocol{Read})
    File f = new File();
         ^
NotOk.java:22: error: [f was moved to a different closure] (f was moved to a different closure)
      return f.read();
             ^
NotOk.java:27: error: [Object did not complete its protocol. Type: FileProtocol{Read}] (Object did not complete its protocol. Type: FileProtocol{Read})
  public static void use(File f) {
                              ^
4 errors```
