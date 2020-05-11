## Original Mungo's output

```
```

## Mungo Checker's output

```
CMain.java:102: error: [Cannot call receive_httpvStrFromS on state State0 (got: State13, State0)] (Cannot call receive_httpvStrFromS on state State0 (got: State13, State0))
        String payload12 = currentC.receive_httpvStrFromS();
                                                         ^
CRole.java:62: error: [Cannot call print on null] (Cannot call print on null)
        this.socketSOut.print("");
                             ^
CRole.java:154: error: [Cannot call read on null] (Cannot call read on null)
                i = socketSIn.read();
                                  ^
CRole.java:169: error: [Cannot call read on null] (Cannot call read on null)
				i = socketSIn.read();
				                  ^
CRole.java:188: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:199: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
6 errors```
