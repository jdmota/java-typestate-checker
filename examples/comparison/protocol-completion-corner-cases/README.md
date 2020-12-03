## Mungo's output

```
Exception in thread "main" java.lang.NullPointerException
	at org.extendj.ast.Declarator.typestateCheck(Declarator.java:157)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:610)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.ASTNode.collectTypestate(ASTNode.java:612)
	at org.extendj.ast.Program.collect(Program.java:582)
	at org.extendj.ast.Program.compile(Program.java:604)
	at org.extendj.TypestateChecker.run(TypestateChecker.java:32)
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)```

## Our tool's output

```
NotOk.java:6: error: [Passing an object with protocol to a method that cannot be analyzed] (Passing an object with protocol to a method that cannot be analyzed)
    list.add(new File());
             ^
NotOk.java:10: error: [Object did not complete its protocol. Type: State "Read" | Ended | Moved] (Object did not complete its protocol. Type: State "Read" | Ended | Moved)
    public File file = new File();
                ^
2 errors```
