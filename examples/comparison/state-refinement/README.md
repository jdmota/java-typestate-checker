## Mungo's output

```
NotOk.java:21: error: annotation type org.checkerframework.checker.mungo.lib.MungoState is not applicable to this kind of declaration
Ok.java:20: error: annotation type org.checkerframework.checker.mungo.lib.MungoState is not applicable to this kind of declaration

NotOk.java: 13-14: Semantic Error
		Object reference is used uninitialised.

Ok.java: 12-14: Semantic Error
		Object reference is used uninitialised.
NotOk.java:21: error: annotation type org.checkerframework.checker.mungo.lib.MungoState is not applicable to this kind of declaration
Ok.java:20: error: annotation type org.checkerframework.checker.mungo.lib.MungoState is not applicable to this kind of declaration```

## Our tool's output

```
NotOk.java:13: error: [argument.type.incompatible] incompatible types in argument.
        read(f);
             ^
  found   : FileProtocol{Close} File
  required: FileProtocol{Read} File
1 error```
