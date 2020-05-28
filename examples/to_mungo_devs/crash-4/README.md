## Current Mungo's output

```
Exception in thread "main" java.lang.NullPointerException
	at org.extendj.ast.VarAccess.getTypestateVar_compute(VarAccess.java:920)
	at org.extendj.ast.VarAccess.getTypestateVar(VarAccess.java:905)
	at org.extendj.ast.Dot.getTypestateVar(Dot.java:855)
	at org.extendj.ast.Access.getQualifiedTypestateVar(Access.java:397)
	at org.extendj.ast.MethodAccess.getGraph(MethodAccess.java:2007)
	at org.extendj.ast.Dot.getGraph(Dot.java:874)
	at org.extendj.ast.ExprStmt.getGraph(ExprStmt.java:379)
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

