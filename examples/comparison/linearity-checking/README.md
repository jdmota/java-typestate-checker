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
Ok.java:7: error: [f2] did not complete its protocol (found: State{File, Read})
  public static void main2() {
                     ^
Ok.java:2: error: [f] did not complete its protocol (found: State{File, Read})
  public static void main1() {
                     ^
NotOk.java:20: error: Cannot call [read] on Shared{File}
    f.read();
    ^
NotOk.java:33: error: Cannot access [f]
      return f.read();
             ^
NotOk.java:40: error: Cannot call [read] on Shared{File}
    System.out.println(f.read());
                       ^
NotOk.java:4: error: [f] did not complete its protocol (found: State{File, Read})
  public static void main1() {
                     ^
NotOk.java:10: error: [f] did not complete its protocol (found: State{File, Read})
  public static void main2() {
                     ^
NotOk.java:16: error: [f2] did not complete its protocol (found: State{File, Read})
  public static void main3() {
                     ^
NotOk.java:23: error: [f2] did not complete its protocol (found: State{File, Read})
  public static void main4() {
                     ^
10 errors```
