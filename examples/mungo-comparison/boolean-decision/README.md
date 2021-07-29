## Mungo's output

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
JavaIteratorProtocol.protocol:3,37: error: unexpected token "false"```

## Our tool's output

```
NotOk.java:8: error: Cannot call [next] on State{JavaIterator, end}
      System.out.println(it.next());
                                ^
NotOk.java:4: error: [it] did not complete its protocol (found: State{JavaIterator, Next})
  public static void main(String args[]) {
                     ^
JavaIterator.java:19: error: Incompatible return value: cannot cast from Shared{java.lang.Object} | Null to Shared{java.lang.String}
    return it.next();
    ^
3 errors```
