## Mungo's output

```
```

## Java Typestate Checker's output

```
CMain.java:11: error: [assignment.type.incompatible] incompatible types in assignment.
            readline = readerC.readLine();
                                       ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CMain.java:16: error: [return.type.incompatible] incompatible types in return.
        return readline;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CMain.java:102: error: [Cannot call receive_httpvStrFromS on state State0 (got: State13, State0)] (Cannot call receive_httpvStrFromS on state State0 (got: State13, State0))
        String payload12 = currentC.receive_httpvStrFromS();
                                                         ^
CRole.java:37: error: [Cannot call getInputStream on null] (Cannot call getInputStream on null)
            socketSIn = new BufferedReader(new InputStreamReader(socket.getInputStream()));
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
CRole.java:188: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:188: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:193: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:199: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:199: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:204: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:212: error: [Cannot call read on null] (Cannot call read on null)
                i = socketSIn.read();
                                  ^
CRole.java:263: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:263: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:268: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:274: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:274: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:279: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:285: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:285: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:290: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:296: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:296: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:301: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:307: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:307: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:312: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:318: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:318: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:323: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:329: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:329: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:334: error: [argument.type.incompatible] incompatible types in argument.
        return Integer.parseInt(line);
                                ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:340: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:340: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:345: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:351: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:351: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:356: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:362: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:362: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:367: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:373: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:373: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:378: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:384: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:384: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:389: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:395: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:395: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:400: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:406: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:406: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:411: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:417: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:417: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:422: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:428: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:428: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:433: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:439: error: [assignment.type.incompatible] incompatible types in assignment.
            line = this.socketSIn.readLine();
                                          ^
  found   : NoProtocol | Null String
  required: NoProtocol String
CRole.java:439: error: [Cannot call readLine on null] (Cannot call readLine on null)
            line = this.socketSIn.readLine();
                                          ^
CRole.java:444: error: [return.type.incompatible] incompatible types in return.
        return line;
               ^
  type of expression: NoProtocol | Null String
  method return type: NoProtocol String
CRole.java:448: error: [argument.type.incompatible] incompatible types in argument.
        return getString(socketSIn);
                         ^
  found   : NoProtocol | Null BufferedReader
  required: NoProtocol BufferedReader
66 errors```
