## Mungo Checker's output

```
NotOk.java:7: error: [Cannot call hasNext on moved value] (Cannot call hasNext on moved value)
    it.hasNext();
              ^
NotOk.java:13: error: [argument.type.incompatible] incompatible types in argument.
    use(it);
        ^
  found   : Moved JavaIterator
  required: JavaIteratorProtocol{HasNext|Next} JavaIterator
NotOk.java:20: error: [Cannot call hasNext on moved value] (Cannot call hasNext on moved value)
    it.hasNext();
              ^
NotOk.java:27: error: [argument.type.incompatible] incompatible types in argument.
    use(it);
        ^
  found   : Moved JavaIterator
  required: JavaIteratorProtocol{HasNext|Next} JavaIterator
4 errors
```

## Original Mungo's output

```

NotOk.java: 6-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 5. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.

NotOk.java: 12-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 11. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.

NotOk.java: 18-24: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 17. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.

NotOk.java: 25-24: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 0-0: Semantic Error
		Object created at NotOk.java: 24. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.

Ok.java: 0-0: Semantic Error
		Object created at Ok.java: 5. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.

Ok.java: 0-0: Semantic Error
		Object created at Ok.java: 10. Typestate mismatch. Found: String next(), end, Boolean hasNext(). Expected: <True, False>.
```
