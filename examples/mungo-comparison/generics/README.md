## Mungo's output

```
MyComparator.java:5,22: error: no visible type named T
MyComparator.java:5,27: error: no visible type named T
Ok.java:3: error: MyComparator is not a generic type but used as one in MyComparator<Integer>
Ok.java:3: error: MyComparator is not a generic type but used as one in MyComparator<Integer>

MyComparator.java: 0-0: Semantic Error
		Cannot find typestate MyComparatorProtocol defined for class MyComparator.

MyComparator.java: 0-0: Semantic Error
		Cannot find typestate MyComparatorProtocol defined for class MyComparator.
MyComparator.java:5,22: error: no visible type named T
MyComparator.java:5,27: error: no visible type named T
Ok.java:3: error: MyComparator is not a generic type but used as one in MyComparator<Integer>
Ok.java:3: error: MyComparator is not a generic type but used as one in MyComparator<Integer>
MyComparatorProtocol.protocol:1,31: error: unexpected token "<"
MyComparatorProtocol.protocol:6,1: error: unexpected token ""```

## Our tool's output

```
MyComparatorProtocol.protocol:1: error: (mismatched input '<' expecting '{')
typestate MyComparatorProtocol<T> {
                              ^
1 error```
