## Mungo's output

```
NotOk.java:20: error: annotation type jatyc.lib.Ensures is not applicable to this kind of declaration
Ok.java:19: error: annotation type jatyc.lib.Ensures is not applicable to this kind of declaration

NotOk.java: 12-14: Semantic Error
		Object reference is used uninitialised.

Ok.java: 11-14: Semantic Error
		Object reference is used uninitialised.
NotOk.java:20: error: annotation type jatyc.lib.Ensures is not applicable to this kind of declaration
Ok.java:19: error: annotation type jatyc.lib.Ensures is not applicable to this kind of declaration```

## Our tool's output

```
NotOk.java:12: error: Incompatible parameter: cannot cast from State{File, Close} to State{File, Read}
        read(f);
             ^
1 error```
