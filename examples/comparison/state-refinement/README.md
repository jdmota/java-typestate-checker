## Original Mungo's output

```
```

## Mungo Checker's output

```
NotOk.java:10: error: [argument.type.incompatible] incompatible types in argument.
        use(f);
            ^
  found   : FileProtocol{Read} File
  required: FileProtocol{Close} File
NotOk.java:18: error: [Cannot call read on state Close (got: Close)] (Cannot call read on state Close (got: Close))
    f.read();
          ^
2 errors```
