## Mungo's output

```

NotOk.java: 11-13: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 6. Typestate mismatch. Found: end. Expected: void close().

Ok.java: 6-20: Semantic Error
		Object reference is used uninitialised.```

## Our tool's output

```
Ok.java:6: error: Cannot access [args.length]
    @Nullable File f = args.length == 0 ? null : new File();
                           ^
Ok.java:5: error: [new File] did not complete its protocol (found: State{File, Init})
  public static void main(String args[]) {
                     ^
NotOk.java:12: error: Cannot call close on null
        f.close();
         ^
NotOk.java:20: error: Incompatible parameter because Null is not a subtype of State{File, Init}
    use(null);
        ^
NotOk.java:11: error: The previous value of [f] did not complete its protocol (found: State{File, Close})
        f = null;
          ^
5 errors```
