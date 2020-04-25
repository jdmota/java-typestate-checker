## Mungo Checker's output

```
NotOk.java:6: error: [Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext}] (Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext})
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
                 ^
NotOk.java:15: error: [Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext}] (Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext})
    JavaIterator it = new JavaIterator(Arrays.asList(args).iterator());
                 ^
NotOk.java:17: error: [it was moved to a different closure] (it was moved to a different closure)
      return it.hasNext();
             ^
NotOk.java:21: error: [Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext|Next}] (Object did not complete its protocol. Type: JavaIteratorProtocol{HasNext|Next})
  public static void use(JavaIterator it) {
                                      ^
4 errors
```

## Original Mungo's output

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
	at org.extendj.TypestateChecker.main(TypestateChecker.java:18)
```
