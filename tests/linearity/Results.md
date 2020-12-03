## Original Mungo's output

```

Obj.java: 12-5: Semantic Error
		Method call use(Obj) has no target.

Obj.java: 20-5: Semantic Error
		Method call use(Obj, Obj) has no target.

Obj.java: 30-5: Semantic Error
		Method call use(Obj, Obj) has no target.

Obj.java: 12-5: Semantic Error
		Method call use(Obj) has no target.

Obj.java: 20-5: Semantic Error
		Method call use(Obj, Obj) has no target.

Obj.java: 30-5: Semantic Error
		Method call use(Obj, Obj) has no target.

Obj.java: 12-9: Semantic Error
		Object reference is used uninitialised.

Obj.java: 20-9: Semantic Error
		Object reference is used uninitialised.

Obj.java: 20-15: Semantic Error
		Object reference is used uninitialised.

Obj.java: 30-9: Semantic Error
		Object reference is used uninitialised.

Obj.java: 30-14: Semantic Error
		Object reference is used uninitialised.
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
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)
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
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)
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
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)
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
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)
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
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)
```

## Java Typestate Checker's output

```
Obj.java:14: error: [Cannot call finish on moved value] (Cannot call finish on moved value)
    obj.finish();
              ^
Obj.java:22: error: [Cannot call finish on moved value] (Cannot call finish on moved value)
    obj1.finish();
               ^
Obj.java:24: error: [Cannot call finish on moved value] (Cannot call finish on moved value)
    obj2.finish();
               ^
Obj.java:30: error: [argument.type.incompatible] incompatible types in argument.

    use(obj, obj);
             ^
  found   : Moved Obj.Obj

  required: State "Start" Obj
Obj.java:32: error: [Cannot call finish on moved value] (Cannot call finish on moved value)
    obj.finish();
              ^
ObjWithPrivField.java:22: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPrivField.java:32: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPrivField.java:35: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPrivField.java:35: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o2.f = o3;
      ^
ObjWithPrivField.java:45: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPrivField.java:47: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPrivField.java:57: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o1;
      ^
ObjWithPrivField.java:59: error: [Cannot call finish on moved value] (Cannot call finish on moved value)
    o1.finish();
             ^
ObjWithPrivField.java:67: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPrivField.java:70: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o1;
      ^
ObjWithPrivField.java:70: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o2.f = o1;
      ^
ObjWithPrivField.java:79: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPrivField.java:82: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPrivField.java:82: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o2.f = o3;
      ^
ObjWithPrivField.java:85: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o3.f = o1;
      ^
ObjWithPrivField.java:85: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o3.f = o1;
      ^
ObjWithPrivField.java:94: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o3.f = o1;
      ^
ObjWithPrivField.java:96: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPrivField.java:99: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPrivField.java:99: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o1.f = o2;
      ^
ObjWithPubField.java:8: error: [Object did not complete its protocol. Type: State "Start" | Ended | Moved | Null] (Object did not complete its protocol. Type: State "Start" | Ended | Moved | Null)
  public @Nullable ObjWithPubField f = null;
                                        ^
ObjWithPubField.java:13: error: [Cannot call finish on ended protocol, on moved value] (Cannot call finish on ended protocol, on moved value)
      f.finish();
              ^
ObjWithPubField.java:24: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPubField.java:34: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPubField.java:37: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPubField.java:37: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o2.f = o3;
      ^
ObjWithPubField.java:47: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPubField.java:49: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPubField.java:59: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o1;
      ^
ObjWithPubField.java:61: error: [Cannot call finish on moved value] (Cannot call finish on moved value)
    o1.finish();
             ^
ObjWithPubField.java:69: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPubField.java:72: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o1;
      ^
ObjWithPubField.java:72: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o2.f = o1;
      ^
ObjWithPubField.java:81: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPubField.java:84: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPubField.java:84: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o2.f = o3;
      ^
ObjWithPubField.java:87: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o3.f = o1;
      ^
ObjWithPubField.java:87: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o3.f = o1;
      ^
ObjWithPubField.java:96: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o3.f = o1;
      ^
ObjWithPubField.java:98: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o2.f = o3;
      ^
ObjWithPubField.java:101: error: [Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null] (Cannot override because object has not ended its protocol. Type: State "Start" | Ended | Moved | Null)
    o1.f = o2;
      ^
ObjWithPubField.java:101: error: [Cannot access f on moved value] (Cannot access f on moved value)
    o1.f = o2;
      ^
ObjWithSetter.java:36: error: [Cannot call setF on moved value] (Cannot call setF on moved value)
    o2.setF(o3);
           ^
ObjWithSetter.java:56: error: [argument.type.incompatible] incompatible types in argument.

    o1.setF(o1);
            ^
  found   : Moved ObjWithSetter.ObjWithSetter

  required: ObjWithSetter{Start|Set} ObjWithSetter
ObjWithSetter.java:66: error: [Cannot call setF on moved value] (Cannot call setF on moved value)
    o2.setF(o1);
           ^
ObjWithSetter.java:76: error: [Cannot call setF on moved value] (Cannot call setF on moved value)
    o2.setF(o3);
           ^
ObjWithSetter.java:78: error: [Cannot call setF on moved value] (Cannot call setF on moved value)
    o3.setF(o1);
           ^
ObjWithSetter.java:89: error: [Cannot call setF on moved value] (Cannot call setF on moved value)
    o1.setF(o2);
           ^
ObjWithSetter.java:112: error: [Object did not complete its protocol. Type: State "Set"] (Object did not complete its protocol. Type: State "Set")
      ObjWithSetter o1 = new ObjWithSetter();
                    ^
ObjWithSetter.java:115: error: [argument.type.incompatible] incompatible types in argument.

      createChainNotOk(o2, len - 1);
                       ^
  found   : Moved ObjWithSetter

  required: ObjWithSetter{Start|Set} ObjWithSetter
PrivateAccess.java:18: error: [Cannot call finish on ended protocol, on moved value] (Cannot call finish on ended protocol, on moved value)
    w.o.finish();
              ^
PublicAccess.java:8: error: [Object did not complete its protocol. Type: State "Start" | Ended | Moved] (Object did not complete its protocol. Type: State "Start" | Ended | Moved)
  public Obj o = new Obj();
             ^
PublicAccess.java:12: error: [Cannot call finish on ended protocol, on moved value] (Cannot call finish on ended protocol, on moved value)
    o.finish();
            ^
PublicAccess.java:18: error: [Cannot call finish on ended protocol, on moved value] (Cannot call finish on ended protocol, on moved value)
    w.o.finish();
              ^
59 errors
```
