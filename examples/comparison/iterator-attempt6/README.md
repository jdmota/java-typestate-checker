## Mungo's output

```

Main.java: 0-0: Semantic Error
		Object created at Main.java: 5. Typestate mismatch. Found: end, Boolean hasNext(). Expected: Boolean hasNext().```

## Our tool's output

```
JavaIterator.java:14: error: [return.type.incompatible] incompatible types in return.
    return it.hasNext() ? Boolean.True : Boolean.False;
                        ^
  type of expression: Unknown Boolean
  method return type: NoProtocol Boolean
1 error```
