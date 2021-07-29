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
Main.java:9: error: Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end}
      System.out.println(it.next());
                                ^
Main.java:5: error: [it] did not complete its protocol (found: State{JavaIterator, Next} | State{JavaIterator, end})
	public static void main(String[] args) {
	                   ^
JavaIterator.java:19: error: Incompatible return value: cannot cast from Shared{java.lang.Object} | Null to Shared{java.lang.String}
    return it.next();
    ^
3 errors```
