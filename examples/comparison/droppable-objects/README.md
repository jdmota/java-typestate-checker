## Mungo's output

```

MyComparator.java: 0-0: Semantic Error
		Cannot find typestate MyComparatorProtocol defined for class MyComparator.

MyComparator.java: 0-0: Semantic Error
		Cannot find typestate MyComparatorProtocol defined for class MyComparator.
MyComparatorProtocol.protocol:4,9: error: unexpected token ":"```

## Our tool's output

```
MyComparator.java:6: error: [return.type.incompatible] incompatible types in return.
    return a < b ? -1 : a > b ? 1 : 0;
                 ^
  type of expression: Unknown int
  method return type: Primitive int
1 error```
