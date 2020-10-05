## Original Mungo's output

```
Exception in thread "main" java.lang.NullPointerException
	at org.extendj.ast.MethodAccess.getTypestateVar(MethodAccess.java:1909)
	at org.extendj.ast.Dot.getTypestateVar(Dot.java:855)
	at org.extendj.ast.Declarator.getGraph(Declarator.java:855)
	at org.extendj.ast.VarDeclStmt.getGraph(VarDeclStmt.java:567)
	at org.extendj.ast.Block.getGraph(Block.java:723)
	at org.extendj.ast.MethodDecl.getGraph(MethodDecl.java:2202)
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

## Mungo Checker's output

```
Main.java:7: error: [Object did not complete its protocol. Type: FileProtocol{Read} | Ended | Moved] (Object did not complete its protocol. Type: FileProtocol{Read} | Ended | Moved)
    File f1 = list.get(0);
         ^
Main.java:6: error: [Passing an object with protocol to a method that cannot be analyzed] (Passing an object with protocol to a method that cannot be analyzed)
    list.add(new File());
             ^
Main.java:7: error: [assignment.type.incompatible] incompatible types in assignment.
    File f1 = list.get(0);
                      ^
  found   : FileProtocol{Read} | Ended | Moved File
  required: FileProtocol{Read} File
3 errors```
