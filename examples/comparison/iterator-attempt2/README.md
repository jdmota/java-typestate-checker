## Mungo's output

```

JavaIteratorProtocol.protocol: 3-5: Semantic Error
		Method boolean hasNext() should return an enumeration type.

JavaIteratorProtocol.protocol: 3-24: Semantic Error
		Duplicate case label: .

Main.java: 0-0: Semantic Error
		Object created at Main.java: 5. Typestate mismatch. Found: String next(), end, boolean hasNext(). Expected: <, >.

JavaIteratorProtocol.protocol: 3-5: Semantic Error
		Method boolean hasNext() should return an enumeration type.

JavaIteratorProtocol.protocol: 3-24: Semantic Error
		Duplicate case label: .
JavaIteratorProtocol.protocol:3,25: error: unexpected token "true"
JavaIteratorProtocol.protocol:3,37: error: unexpected token "false"```

## Our tool's output

```
JavaIterator.java:18: error: Incompatible return value: cannot cast from Shared{java.lang.Object} | Null to Shared{java.lang.String}
    return it.next();
    ^
1 error```
