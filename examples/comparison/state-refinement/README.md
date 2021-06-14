## Mungo's output

```
NotOk.java:21: error: annotation type jatyc.lib.State is not applicable to this kind of declaration
Ok.java:20: error: annotation type jatyc.lib.State is not applicable to this kind of declaration

NotOk.java: 13-14: Semantic Error
		Object reference is used uninitialised.

Ok.java: 12-14: Semantic Error
		Object reference is used uninitialised.
NotOk.java:21: error: annotation type jatyc.lib.State is not applicable to this kind of declaration
Ok.java:20: error: annotation type jatyc.lib.State is not applicable to this kind of declaration```

## Our tool's output

```
NotOk.java:25: error: Parameters with @Ensures should be final
  public static void read(@Requires("Read") @Ensures("Close") File f) {
                                            ^
Ok.java:24: error: Parameters with @Ensures should be final
  public static void read(@Requires("Read") @Ensures("Close") File f) {
                                            ^
NotOk.java:13: error: Incompatible parameter because State{File, Close} is not a subtype of State{File, Read}
        read(f);
             ^
3 errors```
