## Mungo Checker's output

```
Main.java:5: error: [Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext} | Ended] (Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext} | Ended)
		JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
		             ^
1 error
```

## Original Mungo's output

```

Main.java: 0-0: Semantic Error
		Object created at Main.java: 5. Typestate mismatch. Found: end, Boolean hasNext(). Expected: Boolean hasNext().
```
