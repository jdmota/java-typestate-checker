## Mungo's output

```

JavaIteratorProtocol.protocol: 5-5: Semantic Error
		Method Boolean hasNext() should return an enumeration type.

Main.java: 0-0: Semantic Error
		Object created at Main.java: 6. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.

JavaIteratorProtocol.protocol: 5-5: Semantic Error
		Method Boolean hasNext() should return an enumeration type.```

## Our tool's output

```
JavaIterator.java:15: error: [return.type.incompatible] incompatible types in return.
    return it.hasNext() ? Boolean.True : Boolean.False;
                        ^
  type of expression: Unknown Boolean
  method return type: NoProtocol Boolean
1 error```
