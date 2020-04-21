## Mungo Checker's output

```
JavaIterator.java:6: error: [Class has no public method for transition Boolean hasNext() on state HasNext] (Class has no public method for transition Boolean hasNext() on state HasNext)
public class JavaIterator {
       ^
JavaIterator.java:6: error: [Expected decision state with two labels (true/false) in transition Boolean hasNext() on state HasNext] (Expected decision state with two labels (true/false) in transition Boolean hasNext() on state HasNext)
public class JavaIterator {
       ^
Main.java:8: error: [Cannot call hasNext on state HasNext (got: HasNext)] (Cannot call hasNext on state HasNext (got: HasNext))
    while(it.hasNext() == Boolean.True){
                    ^
3 errors
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
