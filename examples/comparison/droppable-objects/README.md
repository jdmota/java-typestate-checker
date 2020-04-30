## Original Mungo's output

```

Ok.java: 0-0: Semantic Error
		Object created at Ok.java: 3. Typestate mismatch. Found: end. Expected: int compare(int, int).```

## Mungo Checker's output

```
Ok.java:3: error: [Object did not complete its protocol. Type: MyComparatorProtocol{Start}] (Object did not complete its protocol. Type: MyComparatorProtocol{Start})
		MyComparator comparator = new MyComparator();
		             ^
1 error```
