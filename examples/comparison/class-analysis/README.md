## Original Mungo's output

```

NotOkFileWrapper1.java: 7-31: Semantic Error
		Object reference is used uninitialised.```

## Mungo Checker's output

```
NotOkFileWrapper1.java:9: error: [Object did not complete its protocol. Type: FileProtocol{Read}] (Object did not complete its protocol. Type: FileProtocol{Read})
  public void init(File file) {}
                        ^
NotOkFileWrapper1.java:12: error: [Cannot call read on null] (Cannot call read on null)
    return file.read();
                    ^
NotOkFileWrapper1.java:16: error: [Cannot call close on null] (Cannot call close on null)
    file.close();
              ^
NotOkFileWrapper2.java:7: error: [Object did not complete its protocol. Type: FileProtocol{Read}] (Object did not complete its protocol. Type: FileProtocol{Read})
  private @MungoNullable File file = null;
                              ^
NotOkFileWrapper3.java:7: error: [Object did not complete its protocol. Type: FileProtocol{Read}] (Object did not complete its protocol. Type: FileProtocol{Read})
  private @MungoNullable File file = null;
                              ^
NotOkFileWrapper3.java:14: error: [Cannot call close on ended protocol] (Cannot call close on ended protocol)
    file.close();
              ^
NotOkFileWrapper3.java:19: error: [Cannot call read on ended protocol] (Cannot call read on ended protocol)
    file.read();
             ^
7 errors```
