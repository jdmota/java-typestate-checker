## Mungo's output

```

NotOkFileWrapper1.java: 7-26: Semantic Error
		Object reference is used uninitialised.```

## Our tool's output

```
OkFileWrapper.java:18: error: Cannot call [close] on Shared{File}
    file.close();
    ^
OkFileWrapper.java:14: error: Cannot call [read] on Shared{File}
    return file.read();
           ^
NotOkFileWrapper3.java:14: error: Cannot call [close] on Shared{File}
    file.close();
    ^
NotOkFileWrapper3.java:19: error: Cannot call [read] on Shared{File}
    file.read();
    ^
NotOkFileWrapper2.java:14: error: Cannot call [read] on Shared{File}
    return file.read();
           ^
NotOkFileWrapper1.java:16: error: Cannot call close on null
    file.close();
        ^
NotOkFileWrapper1.java:12: error: Cannot call read on null
    return file.read();
               ^
7 errors```
