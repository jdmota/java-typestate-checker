## Mungo's output

```

NotOk.java: 3-14: Semantic Error
		Object created at NotOk.java: 3. Typestate mismatch. Found: String read(). Expected: FileStatus open().```

## Our tool's output

```
NotOk.java:5: error: [Cannot call read on state Init (got: Init)] (Cannot call read on state Init (got: Init))
    System.out.println(f.read());
                             ^
1 error```
