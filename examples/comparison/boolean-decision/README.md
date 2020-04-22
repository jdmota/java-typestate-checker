## Mungo Checker's output

```
NotOk.java:5: error: [Object did not complete its protocol. Type: JavaIteratorProtocol{Next}] (Object did not complete its protocol. Type: JavaIteratorProtocol{Next})
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
                 ^
NotOk.java:8: error: [Cannot call next on ended protocol] (Cannot call next on ended protocol)
      System.out.println(it.next());
                                ^
2 errors
```

## Original Mungo's output

```

JavaIteratorProtocol.protocol: 3-5: Semantic Error
		Method boolean hasNext() should return an enumeration type.

JavaIteratorProtocol.protocol: 3-24: Semantic Error
		Duplicate case label: .

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 5. Typestate mismatch. Found: String next(), end, boolean hasNext(). Expected: <, >.

Ok.java: 0-0: Semantic Error
		Object created at Ok.java: 5. Typestate mismatch. Found: String next(), end, boolean hasNext(). Expected: <, >.

JavaIteratorProtocol.protocol: 3-5: Semantic Error
		Method boolean hasNext() should return an enumeration type.

JavaIteratorProtocol.protocol: 3-24: Semantic Error
		Duplicate case label: .
JavaIteratorProtocol.protocol:3,25: error: unexpected token "true"
JavaIteratorProtocol.protocol:3,37: error: unexpected token "false"
```
