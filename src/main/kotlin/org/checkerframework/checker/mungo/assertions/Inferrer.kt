package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.*
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.utils.treeToElement
import org.checkerframework.checker.mungo.utils.treeToType
import org.checkerframework.dataflow.cfg.ControlFlowGraph
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.block.*
import org.checkerframework.dataflow.cfg.node.LocalVariableNode
import org.checkerframework.dataflow.cfg.node.Node
import org.checkerframework.framework.flow.CFCFGBuilder
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import java.util.*
import javax.lang.model.element.Element
import javax.lang.model.type.TypeMirror

class Inferrer(private val checker: MungoChecker) {

  val utils get() = checker.utils

  private val processingEnv = checker.processingEnvironment
  private lateinit var root: JCTree.JCCompilationUnit

  fun setRoot(root: CompilationUnitTree) {
    this.root = root as JCTree.JCCompilationUnit
  }

  fun run(classTree: ClassTree) {
    val classQueue: Queue<ClassTree> = ArrayDeque()
    classQueue.add(classTree)

    while (!classQueue.isEmpty()) {
      val ct = classQueue.remove() as JCTree.JCClassDecl
      val info = prepareClass(ct)
      run(classQueue, ct, info.static, true)
      run(classQueue, ct, info.nonStatic, false)
    }
  }

  private fun run(classQueue: Queue<ClassTree>, classTree: JCTree.JCClassDecl, info: ClassInfo, isStatic: Boolean) {
    val lambdaQueue: Queue<LambdaExpressionTree> = ArrayDeque()

    // Analyze fields
    // TODO consider fields initialization outside the constructors
    for (field in info.fields) {
      val initializer = field.initializer
      if (initializer != null) {
        run(
          classQueue,
          lambdaQueue,
          UnderlyingAST.CFGStatement(field, classTree),
          isStatic
        )
      }
    }

    // Analyze blocks
    // TODO consider fields initialization outside the constructors
    for (block in info.blocks) {
      run(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGStatement(block, classTree),
        isStatic
      )
    }

    // Analyze methods
    for (method in info.methods) {
      run(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGMethod(method, classTree),
        isStatic
      )
    }

    // Analyze lambdas
    while (!lambdaQueue.isEmpty()) {
      val lambda = lambdaQueue.poll()
      val mt = TreeUtils.enclosingOfKind(utils.getPath(lambda, root), Tree.Kind.METHOD) as MethodTree
      run(
        classQueue,
        lambdaQueue,
        UnderlyingAST.CFGLambda(lambda, classTree, mt),
        isStatic
      )
    }
  }

  private fun astToTree(ast: UnderlyingAST) = when (ast) {
    is UnderlyingAST.CFGMethod -> ast.method
    is UnderlyingAST.CFGLambda -> ast.code
    is UnderlyingAST.CFGStatement -> ast.code
    else -> throw RuntimeException("unknown ast")
  }

  private val locationsGatherer = LocationsGatherer(this)
  private val cfgCache = WeakIdentityHashMap<Tree, ControlFlowGraph>()
  private val constraintsInference = ConstraintsInference()
  val preConditions = mutableMapOf<Node, Assertion>()
  val postConditions = mutableMapOf<Node, Assertion>()
  val specialBlocksConditions = mutableMapOf<SpecialBlock, Assertion>()

  private fun run(
    classQueue: Queue<ClassTree>,
    lambdaQueue: Queue<LambdaExpressionTree>,
    ast: UnderlyingAST,
    isStatic: Boolean
  ) {
    val tree = astToTree(ast)
    val cfg = cfgCache[tree] ?: run {
      val g = CFCFGBuilder.build(root, ast, processingEnv)
      cfgCache[tree] = g
      g
    }

    // Handle method parameters
    val parameters = when (ast) {
      is UnderlyingAST.CFGMethod -> ast.method.parameters.map { LocalVariableNode(it) }
      is UnderlyingAST.CFGLambda -> ast.lambdaTree.parameters.map { LocalVariableNode(it) }
      else -> null
    }

    when (ast) {
      is UnderlyingAST.CFGMethod -> println("${ast.method.name} ${locationsGatherer.getLocations(ast, isStatic)}")
    }

    // Run
    traverse(Assertion(), cfg.entryBlock)

    // Queue classes
    for (cls in cfg.declaredClasses) {
      classQueue.add(cls)
    }

    // Queue lambdas
    for (lambda in cfg.declaredLambdas) {
      lambdaQueue.add(lambda)
    }
  }

  private fun traverse(pre: Assertion, block: Block) {
    val seen = mutableSetOf<Block>()
    if (seen.contains(block)) {
      // TODO also connect here
      return
    }
    seen.add(block)
    when (block) {
      is RegularBlock -> {
        var last = pre

        for (n in block.nodes) {
          last = traverse(last, n)
        }

        block.successor?.let { traverse(last, it) }
      }
      is ExceptionBlock -> {
        val last = traverse(pre, block.node)

        block.successor?.let { traverse(last, it) }

        // TODO handle possible exceptions
      }
      is ConditionalBlock -> {

        traverse(pre, block.thenSuccessor)

        traverse(pre, block.elseSuccessor)

      }
      is SpecialBlock -> {
        specialBlocksConditions[block] = pre

        block.successor?.let { traverse(pre, it) }

      }
      else -> throw RuntimeException("Unexpected block type: " + block.type)
    }
  }

  private fun traverse(prepre: Assertion, node: Node): Assertion {
    val pre = Assertion()
    prepre.implies(pre)
    preConditions[node] = pre

    val result = node.accept(constraintsInference, pre)
    postConditions[node] = result
    return result
  }

  fun print() {
    for ((block, assertion) in specialBlocksConditions) {
      println(block)
      println(assertion)
    }
    println("-----")
    for (node in preConditions.keys) {
      println(preConditions[node])
      println(node)
      println(postConditions[node])
    }
  }

}
