## Mungo's output

```

NotOk.java: 6-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 12-9: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 18-15: Semantic Error
		Object reference is used uninitialised.

NotOk.java: 25-15: Semantic Error
		Object reference is used uninitialised.```

## Our tool's output

```
Ok.java:14: error: Cannot call [read] on Shared{File}
    System.out.println(f.read());
                             ^
Ok.java:4: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f);
        ^
Ok.java:10: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f2);
        ^
NotOk.java:12: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f);
        ^
NotOk.java:19: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f2);
        ^
NotOk.java:26: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f2);
        ^
NotOk.java:20: error: Cannot call [read] on Shared{File}
    f.read();
          ^
NotOk.java:33: error: Cannot access [f]
      return f.read();
             ^
NotOk.java:6: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{File}
    use(f);
        ^
NotOk.java:40: error: Cannot call [read] on Shared{File}
    System.out.println(f.read());
                             ^
10 errors```
