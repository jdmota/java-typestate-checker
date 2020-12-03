## Mungo's output

```
Exception in thread "main" java.lang.NullPointerException
	at org.extendj.ast.MethodDecl.getGraph(MethodDecl.java:2186)
	at org.extendj.ast.ClassDecl.getGraph_compute(ClassDecl.java:2586)
	at org.extendj.ast.ClassDecl.getGraph(ClassDecl.java:2550)
	at org.extendj.ast.ClassDecl.typestateCheck(ClassDecl.java:220)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:610)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.Program.collect(Program.java:582)
	at org.extendj.ast.Program.compile(Program.java:604)
	at org.extendj.TypestateChecker.run(TypestateChecker.java:32)
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)```

## Our tool's output

```
NotOkFileWrapper4.java:5: error: [Object did not complete its protocol. Type: State "Read" | Null] (Object did not complete its protocol. Type: State "Read" | Null)
  private @Nullable File file = null;
                         ^
NotOkFileWrapper4.java:8: error: [Cannot override because object has not ended its protocol. Type: State "Read" | Null] (Cannot override because object has not ended its protocol. Type: State "Read" | Null)
    this.file = file;
        ^
NotOkFileWrapper4.java:12: error: [Cannot call read on null] (Cannot call read on null)
    return file.read();
                    ^
3 errors```
