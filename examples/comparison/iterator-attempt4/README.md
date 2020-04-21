## Mungo Checker's output

```
Main.java:5: error: [Object did not complete its protocol. Type: JavaIteratorProtocol{Next} | Ended] (Object did not complete its protocol. Type: JavaIteratorProtocol{Next} | Ended)
		JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
		             ^
Main.java:8: error: [Cannot call next on ended protocol] (Cannot call next on ended protocol)
      System.out.println(it.next());
                                ^
2 errors
```

## Original Mungo's output

```

Main.java: 0-0: Semantic Error
		Object created at Main.java: 5. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.
```
