## Mungo's output

```
```

## Our tool's output

```
Main.java:6: error: [argument.type.incompatible] incompatible types in argument.
    System.out.println(it.next());
                              ^
  found   : NoProtocol | Null /*INFERENCE FAILED for:*/ ? extends String
  required: NoProtocol String
Main.java:6: error: [Cannot call next on state HasNext (got: HasNext)] (Cannot call next on state HasNext (got: HasNext))
    System.out.println(it.next());
                              ^
2 errors```
