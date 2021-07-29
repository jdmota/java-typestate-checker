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
NotOk.java:9: error: [this.file] did not complete its protocol (found: Shared{File} | State{File, ?})
  public static class FileWrapper {
                ^
NotOk.java:6: error: Incompatible parameter: cannot cast from State{File, Read} to Shared{java.lang.Object} | Null
    list.add(new File());
             ^
NotOk.java:9: error: [this.file] did not complete its protocol (found: Shared{File} | State{File, ?})
  public static class FileWrapper {
                ^
3 errors```
