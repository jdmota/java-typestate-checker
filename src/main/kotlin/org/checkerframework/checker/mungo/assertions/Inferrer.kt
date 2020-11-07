package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.MungoStateType
import org.checkerframework.checker.mungo.typecheck.MungoUnknownType
import org.checkerframework.checker.mungo.typestate.graph.Graph
import org.checkerframework.checker.mungo.utils.treeToType
import org.checkerframework.dataflow.analysis.Store
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.block.*
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.framework.flow.CFCFGBuilder
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import java.util.*
import javax.annotation.processing.ProcessingEnvironment
import javax.lang.model.element.ElementKind
import javax.lang.model.type.TypeKind
import org.checkerframework.checker.mungo.analysis.getReference as getBasicReference

class Inferrer(val checker: MungoChecker) {

  val utils get() = checker.utils
  val processingEnv: ProcessingEnvironment = checker.processingEnvironment
  lateinit var root: JCTree.JCCompilationUnit

  private var firstTime = true

  fun setRoot(root: CompilationUnitTree) {
    this.root = root as JCTree.JCCompilationUnit

    if (firstTime) {
      firstTime = false

      val ref = UnknownRef(utils.typeUtils.nullType)
      unknownInfo = SymbolicInfo(ref, null)
    }
  }

  val locationsGatherer = LocationsGatherer(checker)

  private val assertions = IdentityHashMap<Node, NodeAssertions>()
  private val assertionsList = mutableListOf<Pair<Node, NodeAssertions>>()
  private val preAssertions = IdentityHashMap<UnderlyingAST, NodeAssertions>()
  private val postAssertions = IdentityHashMap<UnderlyingAST, NodeAssertions>()
  private val constraints = Constraints()
  private lateinit var unknownInfo: SymbolicInfo

  private val symToTree = mutableMapOf<Symbol.MethodSymbol, MethodTree>()

  fun symToMethod(sym: Symbol.MethodSymbol): MethodTree? {
    return symToTree.computeIfAbsent(sym) {
      // With "computeIfAbsent", null values are NOT saved in the map
      checker.utils.treeUtils.getTree(sym)
    }
  }

  private val lambdaThreads = mutableMapOf<JCTree.JCLambda, LambdaThread>()
  private val graphToLambdaThread = mutableMapOf<Graph, LambdaThread>()

  fun lambdaThread(lambda: JCTree.JCLambda): LambdaThread {
    return lambdaThreads.computeIfAbsent(lambda) {
      val l = LambdaThread.create(utils, it)
      graphToLambdaThread[l.graph] = l

      l.graph.getAllConcreteStates().forEach { state ->
        constraints.addType(MungoStateType.create(l.graph, state))
      }
      l
    }
  }

  fun analyzeMaybeThreadCreation(node: Node): LambdaThread? {
    if (node is ObjectCreationNode) {
      val tree = node.tree!!
      val constructor = TreeUtils.elementFromUse(tree) as Symbol.MethodSymbol
      val className = constructor.enclosingElement.flatName().toString()
      if (className == "java.lang.Thread") {
        val arg0 = tree.arguments.firstOrNull()
        if (arg0 is JCTree.JCLambda) {
          return lambdaThread(arg0)
        }
      }
    }
    return null
  }

  fun phase1(classTree: ClassTree) {
    val classQueue: Queue<Pair<ClassTree, SymbolicAssertionSkeleton?>> = ArrayDeque()
    classQueue.add(Pair(classTree, null))

    while (!classQueue.isEmpty()) {
      val qel = classQueue.remove()
      val ct = qel.first as JCTree.JCClassDecl
      val outerSkeleton = qel.second

      utils.classUtils.visitClassSymbol(ct.sym)?.let { graph ->
        graph.getAllConcreteStates().forEach {
          constraints.addType(MungoStateType.create(graph, it))
        }
      }

      val info = prepareClass(ct)
      phase1(classQueue, ct, info.static, outerSkeleton)
      phase1(classQueue, ct, info.nonStatic, outerSkeleton)
    }
  }

  private fun phase1(
    classQueue: Queue<Pair<ClassTree, SymbolicAssertionSkeleton?>>,
    classTree: JCTree.JCClassDecl,
    info: ClassInfo,
    outerSkeleton: SymbolicAssertionSkeleton?
  ) {
    val lambdaQueue: Queue<Pair<LambdaExpressionTree, SymbolicAssertionSkeleton>> = ArrayDeque()

    // Analyze fields
    for (field in info.fields) {
      /*if ((field as JCTree.JCVariableDecl).initializer == null) {
        val nullTree = utils.maker.Literal(TypeTag.BOT, null)
        nullTree.pos = field.pos
        field.init = nullTree
      }*/
      if (field.initializer != null) {
        phase1(
          classQueue,
          lambdaQueue,
          UnderlyingAST.CFGStatement(field, classTree),
          outerSkeleton
        )
      }
    }

    // Analyze blocks
    for (block in info.blocks) {
      phase1(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGStatement(block, classTree),
        outerSkeleton
      )
    }

    // Analyze methods
    for (method in info.methods) {
      val m = method as JCTree.JCMethodDecl
      symToTree[m.sym] = m

      phase1(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGMethod(method, classTree),
        outerSkeleton
      )
    }

    // Analyze lambdas
    while (!lambdaQueue.isEmpty()) {
      val lambdaPair = lambdaQueue.poll()
      val mt = TreeUtils.enclosingOfKind(utils.getPath(lambdaPair.first, root), Tree.Kind.METHOD) as MethodTree
      phase1(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGLambda(lambdaPair.first, classTree, mt),
        lambdaPair.second
      )
    }
  }

  private fun astToTree(ast: UnderlyingAST) = when (ast) {
    is UnderlyingAST.CFGMethod -> ast.method
    is UnderlyingAST.CFGLambda -> ast.lambdaTree
    is UnderlyingAST.CFGStatement -> ast.code
    else -> throw RuntimeException("unknown ast")
  }

  private fun astToName(ast: UnderlyingAST) = when (ast) {
    is UnderlyingAST.CFGMethod -> ast.method.name.toString()
    is UnderlyingAST.CFGLambda -> "lambda"
    is UnderlyingAST.CFGStatement -> "statement"
    else -> throw RuntimeException("unknown ast")
  }

  private val cfgCache = IdentityHashMap<Tree, ControlFlowGraph>()

  private fun getCFG(ast: UnderlyingAST): ControlFlowGraph {
    val tree = astToTree(ast)
    return cfgCache.computeIfAbsent(tree) {
      CFCFGBuilder.build(root, ast, processingEnv)
    }
  }

  private fun getCFG(tree: Tree): ControlFlowGraph {
    return cfgCache[tree] ?: error("No CFG found")
  }

  private lateinit var currentSkeleton: SymbolicAssertionSkeleton

  private fun phase1(
    classQueue: Queue<Pair<ClassTree, SymbolicAssertionSkeleton?>>,
    lambdaQueue: Queue<Pair<LambdaExpressionTree, SymbolicAssertionSkeleton>>,
    ast: UnderlyingAST,
    outerSkeleton: SymbolicAssertionSkeleton?
  ) {
    // Generate the CFG
    val cfg = getCFG(ast)

    // Assertion's skeleton
    val skeleton = createSkeleton(outerSkeleton, cfg)

    // Associate assertions before and after each node, and connect implications
    phase1(cfg)

    // Consider threads
    for (node in cfg.allNodes) {
      analyzeMaybeThreadCreation(node)
    }

    // Queue classes
    for (cls in cfg.declaredClasses) {
      classQueue.add(Pair(cls, skeleton))
    }

    // Queue lambdas
    for (lambda in cfg.declaredLambdas) {
      lambdaQueue.add(Pair(lambda, skeleton))
    }
  }

  // TODO optimize so that the assertions do not include unnecessary references (e.g. variable that are not accessible at some program points)
  // TODO use OuterContextRef in all references
  private fun createSkeleton(outerSkeleton: SymbolicAssertionSkeleton?, cfg: ControlFlowGraph): SymbolicAssertionSkeleton {
    // Ref
    val outerRef = outerSkeleton?.ctxRef
    val ref = getCtxRef(outerRef, astToTree(cfg.underlyingAST))

    // Outer locations and equalities
    // val outerLocations = outerSkeleton?.locations ?: emptySet()
    // val outerEqualities = outerSkeleton?.equalities ?: emptySet()

    // fun convert(ref: Reference) = if (outerRef != null && outerLocations.contains(ref)) ref.withNewParent(outerRef) else ref

    // Gather locations and possible equalities
    val locations = gatherLocations(cfg) //.plus(outerLocations)//.mapTo(mutableSetOf()) { convert(it) }
    val equalities = gatherEqualities(cfg, locations) //.plus(outerEqualities)//.mapTo(mutableSetOf()) { (a, b) -> Pair(convert(a), convert(b)) }

    // Save skeleton for the creation of new assertions
    val skeleton = SymbolicAssertionSkeleton(unknownInfo, ref, locations, equalities)
    currentSkeleton = skeleton

    return skeleton
  }

  private fun getCtxRef(parent: OuterContextRef?, tree: Tree): OuterContextRef {
    return OuterContextRef(parent, tree, utils.typeUtils.nullType)
  }

  fun getReference(node: Node): Reference {
    return getDirectReference(node) ?: NodeRef(node)
  }

  fun getDirectReference(node: Node): Reference? {
    return when (node) {
      is ReturnNode -> ReturnSpecialVar(node.type)
      is VariableDeclarationNode -> getBasicReference(LocalVariableNode(node.tree))
      else -> getBasicReference(node)
    }
  }

  fun getOldReference(node: AssignmentNode): OldSpecialVar? {
    if (node.tree is VariableTree) {
      return null
    }
    return OldSpecialVar(getBasicReference(node.target)!!, (node.tree as JCTree).pos)
  }

  fun isConstructor(ast: UnderlyingAST): Boolean {
    return ast is UnderlyingAST.CFGMethod && isConstructor(ast.method)
  }

  fun isConstructor(m: MethodTree): Boolean {
    val method = m as JCTree.JCMethodDecl
    val methodSym = method.sym
    return methodSym.getKind() == ElementKind.CONSTRUCTOR
  }

  private fun gatherLocations(cfg: ControlFlowGraph): Set<Reference> {
    val ast = cfg.underlyingAST
    val locations = locationsGatherer.getParameterLocations(ast).toMutableSet()
    for (node in cfg.allNodes) {
      getReference(node).let { locations.addAll(locationsGatherer.getLocations(it)) }
      if (node is AssignmentNode) {
        getOldReference(node)?.let { locations.addAll(locationsGatherer.getLocations(it)) }
      }
    }
    if (ast is UnderlyingAST.CFGLambda) {
      // Lambdas with only one expression, do not have explicit return nodes
      // So add a location representing the return value
      val lambda = ast.lambdaTree
      if (lambda.bodyKind == LambdaExpressionTree.BodyKind.EXPRESSION) {
        locations.add(ReturnSpecialVar(treeToType(lambda.body)))
      }
    } else if (ast is UnderlyingAST.CFGMethod) {
      // Ensure all methods have a #ret reference,
      // Even constructors and methods that "return" void
      val method = ast.method as JCTree.JCMethodDecl
      val methodSym = method.sym
      if (methodSym.getKind() == ElementKind.CONSTRUCTOR) {
        locations.add(ReturnSpecialVar(methodSym.enclosingElement.asType()))
      } else {
        locations.add(ReturnSpecialVar(methodSym.returnType))
      }
    }
    return locations
  }

  private fun gatherEqualities(cfg: ControlFlowGraph, allLocations: Set<Reference>): PossibleEqualitiesTracker {
    val possibleEqualities = PossibleEqualitiesTracker()

    fun equals(a: Reference, b: Reference) {
      if (a.isPrimitive() || b.isPrimitive()) return
      val aRoot = a.getSimpleRoot()
      val bRoot = b.getSimpleRoot()
      if (aRoot is ClassName || bRoot is ClassName) return
      if (aRoot is NodeRef && bRoot is NodeRef) return
      if (aRoot is NodeRef && aRoot.node !is MethodInvocationNode && aRoot.node !is ObjectCreationNode) return
      if (bRoot is NodeRef && bRoot.node !is MethodInvocationNode && bRoot.node !is ObjectCreationNode) return
      possibleEqualities[a] = b
    }

    // Produce some equalities
    for (node in cfg.allNodes) {
      when (node) {
        is AssignmentNode -> {
          val target = getDirectReference(node.target) ?: continue
          val expression = getDirectReference(node.expression) ?: continue
          equals(target, expression)
        }
        is ReturnNode -> {
          val result = node.result ?: continue
          val target = getDirectReference(node) ?: continue
          val expression = getDirectReference(result) ?: continue
          equals(target, expression)
        }
        // TODO more? (e.g. eq(old(var),something))
      }
    }

    // Additional pairings
    for (a in allLocations) {
      for (b in allLocations) {
        if (a !== b && a.type === b.type) {
          equals(a, b)
        }
      }
    }
    return possibleEqualities
  }

  private fun phase1(cfg: ControlFlowGraph) {
    val ast = cfg.underlyingAST

    // Entry
    val preAndPost = currentSkeleton.create()
    val entry = NodeAssertions(preAndPost, preAndPost, preAndPost, preAndPost, "entry_${astToName(ast)}")
    preAssertions[ast] = entry

    // Exits
    val preThen = currentSkeleton.create()
    val preElse = preThen // TODO different assertion when the method returns a boolean
    postAssertions[ast] = NodeAssertions(preThen, preElse, preThen, preElse, "exit_${astToName(ast)}")

    // Traverse
    traverse(ast, entry, cfg.entryBlock, Store.FlowRule.EACH_TO_EACH)
  }

  private fun traverse(ast: UnderlyingAST, prev: NodeAssertions, block: Block, flowRule: Store.FlowRule) {
    when (block) {
      is RegularBlock -> {
        var last = prev
        var lastFlow = flowRule
        for (n in block.nodes) {
          last = traverse(last, n, lastFlow) ?: return
          lastFlow = Store.FlowRule.EACH_TO_EACH
        }
        block.successor?.let { traverse(ast, last, it, block.flowRule) }
      }
      is ExceptionBlock -> {
        val last = traverse(prev, block.node, flowRule) ?: return
        block.successor?.let { traverse(ast, last, it, block.flowRule) }
        // TODO handle possible exceptions
      }
      is ConditionalBlock -> {
        block.thenSuccessor?.let { traverse(ast, prev, it, block.thenFlowRule) }
        block.elseSuccessor?.let { traverse(ast, prev, it, block.elseFlowRule) }
      }
      is SpecialBlock -> {
        block.successor?.let { traverse(ast, prev, it, block.flowRule) }
        when (block.specialType!!) {
          SpecialBlock.SpecialBlockType.ENTRY -> {
          }
          SpecialBlock.SpecialBlockType.EXIT -> {
            implies(prev, postAssertions[ast]!!, flowRule)
          }
          SpecialBlock.SpecialBlockType.EXCEPTIONAL_EXIT -> {
            // TODO
          }
        }
      }
      else -> throw RuntimeException("Unexpected block type: " + block.type)
    }
  }

  private fun traverse(prev: NodeAssertions, node: Node, flowRule: Store.FlowRule): NodeAssertions? {
    return if (!assertions.containsKey(node)) {
      val preThen: SymbolicAssertion
      val preElse: SymbolicAssertion
      if (prev.postThen !== prev.postElse) {
        preThen = currentSkeleton.create()
        preElse = currentSkeleton.create()
      } else {
        preThen = currentSkeleton.create()
        preElse = preThen
      }

      val postThen: SymbolicAssertion
      val postElse: SymbolicAssertion
      if (shouldEachToEach(node)) {
        postThen = currentSkeleton.create()
        postElse = currentSkeleton.create()
      } else {
        postThen = currentSkeleton.create()
        postElse = postThen
      }

      val nodeAssertions = NodeAssertions(preThen, preElse, postThen, postElse, node.toString())
      assertions[node] = nodeAssertions
      assertionsList.add(Pair(node, nodeAssertions))

      implies(prev, nodeAssertions, flowRule)
      nodeAssertions
    } else {
      implies(prev, assertions[node]!!, flowRule)
      null
    }
  }

  private fun implies(prev: NodeAssertions, next: NodeAssertions, flowRule: Store.FlowRule) {
    when (flowRule) {
      Store.FlowRule.EACH_TO_EACH -> {
        constraints.implies(prev.postThen, next.preThen)
        constraints.implies(prev.postElse, next.preElse)
      }
      Store.FlowRule.THEN_TO_BOTH -> {
        constraints.implies(prev.postThen, next.preThen)
        constraints.implies(prev.postThen, next.preElse)
      }
      Store.FlowRule.ELSE_TO_BOTH -> {
        constraints.implies(prev.postElse, next.preThen)
        constraints.implies(prev.postElse, next.preElse)
      }
      Store.FlowRule.THEN_TO_THEN -> {
        constraints.implies(prev.postThen, next.preThen)
      }
      Store.FlowRule.ELSE_TO_ELSE -> {
        constraints.implies(prev.postElse, next.preElse)
      }
    }
  }

  private fun shouldEachToEach(node: Node): Boolean {
    return node.type.kind == TypeKind.BOOLEAN
    /*return when (val block = node.block) {
      is RegularBlock -> {
        val idx = block.nodes.indexOf(node)
        val nextIdx = idx + 1
        if (nextIdx < block.nodes.size) {
          return shouldEachToEach(node, block.nodes[nextIdx])
        }
        return shouldEachToEach(node, block.successor)
      }
      is ExceptionBlock -> return shouldEachToEach(node, block.successor)
      else -> false
    }*/
  }

  private fun shouldEachToEach(node: Node, succ: Block?): Boolean {
    return when (succ) {
      is ConditionalBlock -> true
      is SpecialBlock -> succ.specialType == SpecialBlock.SpecialBlockType.EXIT
      is RegularBlock -> shouldEachToEach(node, succ.nodes.firstOrNull())
      else -> false
    }
  }

  private fun shouldEachToEach(node: Node?, after: Node?): Boolean {
    return when (after) {
      is ReturnNode -> after.result === node && node?.type?.kind == TypeKind.BOOLEAN
      is ConditionalNotNode -> after.operand === node
      else -> false
    }
  }

  fun getMethodPre(sym: Symbol.MethodSymbol): SymbolicAssertion? {
    val tree = symToMethod(sym) ?: return null
    return getTreePre(tree)
  }

  fun getTreePre(tree: Tree): SymbolicAssertion {
    val cfg = getCFG(tree)
    val assertions = preAssertions[cfg.underlyingAST] ?: error("No assertion for this tree")
    return assertions.preThen
  }

  fun getMethodPost(sym: Symbol.MethodSymbol): Pair<SymbolicAssertion, SymbolicAssertion>? {
    val tree = symToMethod(sym) ?: return null
    return getTreePost(tree)
  }

  fun getTreePost(tree: Tree): Pair<SymbolicAssertion, SymbolicAssertion> {
    val cfg = getCFG(tree)
    val assertions = postAssertions[cfg.underlyingAST] ?: error("No assertion for this tree")
    return Pair(assertions.postThen, assertions.postElse)
  }

  private val isPureCache = IdentityHashMap<Tree, Boolean>()

  fun isPure(ast: UnderlyingAST): Boolean {
    val tree = astToTree(ast)
    return isPureCache.computeIfAbsent(tree) {
      getCFG(it).allNodes.all { node ->
        when (node) {
          is ThisLiteralNode -> true
          is LocalVariableNode -> true
          is FieldAccessNode -> true
          is ReturnNode -> true
          is ValueLiteralNode -> true
          else -> false
        }
      }
    }
  }

  fun phase2() {
    println("Inferring constraints...")

    constraints.same(unknownInfo.fraction, 0)
    constraints.same(unknownInfo.packFraction, 0)
    constraints.same(unknownInfo.type, MungoUnknownType.SINGLETON)

    val visitor = ConstraintsInference(this, constraints)

    for ((ast, assertions) in preAssertions) {
      visitor.visitInitialAssertion(ast, assertions.preThen)
    }

    for ((node, assertions) in assertionsList) {
      node.accept(visitor, assertions)
    }

    when (val solution = constraints.solve()) {
      is NoSolution -> {
        println("No solution!\n")

        solution.unsatCore.map { z3exprLabel ->
          val (constraint, expr, z3expr) = constraints.getConstraintByLabel(z3exprLabel.toString())
          // println(constraints.formatExpr(z3expr, solution))
          expr
        }.let { list ->
          list.forEach { println(it) }
          Simplifier(true, setEqualsToFalse = true).simplifyAll(list).forEach {
            println(it)
          }
        }
      }
      is UnknownSolution -> {
        println("Unknown. Reason: ${solution.reason}\n")
      }
      is Solution -> {
        println("Correct!\n")

        for ((node, assertions) in assertionsList) {
          if (solution.skipNode(node)) continue
          assertions.debug(solution, "--> $node")
        }

        for ((ast, assertions) in postAssertions) {
          val a = preAssertions[ast]!!
          NodeAssertions(
            a.preThen,
            a.preElse,
            assertions.postThen,
            assertions.postElse,
            null
          ).debug(solution, "--> method: ${astToName(ast)}")
        }
      }
      is IncompleteSolution -> {
        println("Found SAT access permissions but no types match\n")

        for ((node, assertions) in assertionsList) {
          if (solution.skipNode(node)) continue
          assertions.debug(solution, "--> $node")
        }

        for ((ast, assertions) in postAssertions) {
          val a = preAssertions[ast]!!
          NodeAssertions(
            a.preThen,
            a.preElse,
            assertions.postThen,
            assertions.postElse,
            null
          ).debug(solution, "--> method: ${astToName(ast)}")
        }

        solution.unsatCore?.map { z3exprLabel ->
          val (constraint, expr, z3expr) = constraints.getConstraintByLabel(z3exprLabel.toString())
          // println(constraints.formatExpr(z3expr, solution))
          expr.substitute(SolutionMap(solution))
        }?.let { list ->
          val simplifier = Simplifier(true)
          val simplifiedExprs = simplifier.simplifyAll(list)
          simplifiedExprs.forEach {
            println(it)
            for (symbol in simplifier.getSymbols(it)) {
              println("Symbol $symbol")
              val aliases = simplifier.getSame(symbol)
              for (alias in aliases) {
                // println("Alias $alias")
                when (alias) {
                  is TinySomeFraction -> println(alias.sym.info.debugWhere())
                  is TinySomeType -> println(alias.sym.info.debugWhere())
                  else -> {
                  }
                }
              }
            }
          }
        }
      }
    }
  }

}
