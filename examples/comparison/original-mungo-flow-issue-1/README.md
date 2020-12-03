## Mungo's output

```
```

## Our tool's output

```
JavaIterator.java:14: error: [return.type.incompatible] incompatible types in return.
    return it.hasNext() ? Boolean.True : Boolean.False;
                        ^
  type of expression: Unknown Boolean
  method return type: NoProtocol Boolean
NotOk.java:5: error: [Object did not complete its protocol. Type: State "HasNext" | Ended] (Object did not complete its protocol. Type: State "HasNext" | Ended)
		JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
		             ^
2 errors```
