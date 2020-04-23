## Mungo Checker's output

```
JavaIteratorProtocol.protocol:5: error: (Class JavaIterator has no public method for this transition)
    Boolean hasNext(): <True: Next, False: end>
    ^
JavaIteratorProtocol.protocol:5: error: (Expected decision state with two labels (true/false))
    Boolean hasNext(): <True: Next, False: end>
                       ^
2 errors
```

## Original Mungo's output

```

JavaIteratorProtocol.protocol: 5-5: Semantic Error
		Method Boolean hasNext() should return an enumeration type.

Main.java: 0-0: Semantic Error
		Object created at Main.java: 6. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.

JavaIteratorProtocol.protocol: 5-5: Semantic Error
		Method Boolean hasNext() should return an enumeration type.
```
