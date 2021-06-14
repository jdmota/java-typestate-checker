## Mungo's output

```

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.

Auction.java: 29-17: Semantic Error
		Object reference is used uninitialised.```

## Our tool's output

```
error: SourceChecker.typeProcess: unexpected Throwable (NotImplementedError) while processing Auction.java; message: An operation is not implemented: #helpers.arrayInitWithDimensions not implemented
  ; The Checker Framework crashed.  Please report the crash.
  Compilation unit: Auction.java
  Last visited tree at line 3 column 1:
  @Typestate("AuctionProtocol")
  Exception: kotlin.NotImplementedError: An operation is not implemented: #helpers.arrayInitWithDimensions not implemented; kotlin.NotImplementedError: An operation is not implemented: #helpers.arrayInitWithDimensions not implemented
  	at jatyc.core.adapters.CFAdapter.helperToFuncInterface(CFAdapter.kt:634)
  	at jatyc.core.adapters.CFAdapter.transformHelper(CFAdapter.kt:645)
  	at jatyc.core.adapters.CFAdapter.access$transformHelper(CFAdapter.kt:201)
  	at jatyc.core.adapters.CFAdapter$connect$result$1.apply(CFAdapter.kt:547)
  	at jatyc.core.adapters.CFAdapter$connect$result$1.apply(CFAdapter.kt:201)
  	at java.util.Map.computeIfAbsent(Map.java:957)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:547)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:501)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:492)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:508)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:492)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:504)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:492)
  	at jatyc.core.adapters.CFAdapter.connect(CFAdapter.kt:524)
  	at jatyc.core.adapters.CFAdapter.checkersCFGtoSimpleCFG(CFAdapter.kt:487)
  	at jatyc.core.adapters.CFAdapter.processCFG(CFAdapter.kt:479)
  	at jatyc.core.adapters.CFAdapter.transformClass(CFAdapter.kt:362)
  	at jatyc.core.adapters.CFAdapter.access$transformClass(CFAdapter.kt:201)
  	at jatyc.core.adapters.CFAdapter$transformClass$5.apply(CFAdapter.kt:440)
  	at jatyc.core.adapters.CFAdapter$transformClass$5.apply(CFAdapter.kt:201)
  	at java.util.Map.computeIfAbsent(Map.java:957)
  	at jatyc.core.adapters.CFAdapter.transformClass(CFAdapter.kt:437)
  	at jatyc.core.adapters.CFVisitor.visitClass(CFVisitor.kt:45)
  	at jatyc.core.adapters.CFVisitor.visitClass(CFVisitor.kt:28)
  	at com.sun.tools.javac.tree.JCTree$JCClassDecl.accept(JCTree.java:808)
  	at com.sun.source.util.TreePathScanner.scan(TreePathScanner.java:56)
  	at org.checkerframework.framework.source.SourceVisitor.visit(SourceVisitor.java:82)
  	at org.checkerframework.framework.source.SourceChecker.typeProcess(SourceChecker.java:954)
  	at org.checkerframework.javacutil.AbstractTypeProcessor$AttributionTaskListener.finished(AbstractTypeProcessor.java:190)
  	at com.sun.tools.javac.api.ClientCodeWrapper$WrappedTaskListener.finished(ClientCodeWrapper.java:828)
  	at com.sun.tools.javac.api.MultiTaskListener.finished(MultiTaskListener.java:120)
  	at com.sun.tools.javac.main.JavaCompiler.flow(JavaCompiler.java:1404)
  	at com.sun.tools.javac.main.JavaCompiler.flow(JavaCompiler.java:1363)
  	at com.sun.tools.javac.main.JavaCompiler.compile(JavaCompiler.java:959)
  	at com.sun.tools.javac.main.Main.compile(Main.java:302)
  	at com.sun.tools.javac.main.Main.compile(Main.java:162)
  	at com.sun.tools.javac.Main.compile(Main.java:57)
  	at com.sun.tools.javac.Main.main(Main.java:43)
1 error```
