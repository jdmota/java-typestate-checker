## Mungo Checker's output

```
NotOk.java:3: error: [Object did not complete its protocol. Type: FileProtocol{Read}] (Object did not complete its protocol. Type: FileProtocol{Read})
    File f = new File();
         ^
NotOk.java:7: error: [Cannot call read on ended protocol] (Cannot call read on ended protocol)
        System.out.println(f.read());
                                 ^
2 errors
```

## Original Mungo's output

```

NotOk.java: 10-7: Semantic Error
		Object created at NotOk.java: 3. Typestate mismatch. Found: end. Expected: String read().
```
