package org.checkerframework.checker.mungo.assertions

import com.microsoft.z3.BoolExpr
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement
import javax.lang.model.type.TypeKind

class ConstraintsInference(private val inferrer: Inferrer, private val constraints: Constraints) : AbstractNodeVisitor<Void?, NodeAssertions>() {

  private fun getRef(n: Node) = inferrer.getReference(n)
  private fun getDirectRef(n: Node) = inferrer.getDirectReference(n) ?: error("No reference for $n")
  private fun getInfo(n: Node, a: SymbolicAssertion) = a[getRef(n)]

  private val require = object {
    fun read(node: Node, assertions: NodeAssertions) {
      val thenInfo = getInfo(node, assertions.preThen)
      val elseInfo = getInfo(node, assertions.preElse)

      constraints.notZero(thenInfo.fraction)
      if (thenInfo !== elseInfo) {
        constraints.notZero(elseInfo.fraction)
      }

      if (node is FieldAccessNode) {
        notNull(node.receiver, assertions)
        read(node.receiver, assertions)
      }
    }

    fun write(node: Node, assertions: NodeAssertions) {
      val thenInfo = getInfo(node, assertions.preThen)
      val elseInfo = getInfo(node, assertions.preElse)

      constraints.one(thenInfo.fraction)
      if (thenInfo !== elseInfo) {
        constraints.one(elseInfo.fraction)
      }

      if (node is FieldAccessNode) {
        notNull(node.receiver, assertions)
        read(node.receiver, assertions)
      }
    }

    private fun notNull(node: Node, assertions: NodeAssertions) {
      type(node, assertions, MungoObjectType.SINGLETON)
    }

    fun type(node: Node, assertions: NodeAssertions, type: MungoType) {
      val thenInfo = getInfo(node, assertions.preThen)
      val elseInfo = getInfo(node, assertions.preElse)

      constraints.subtype(thenInfo.type, type)
      if (thenInfo !== elseInfo) {
        constraints.subtype(elseInfo.type, type)
      }
    }
  }

  private val ensures = object {
    fun newVar(info: SymbolicInfo) {
      constraints.one(info.fraction)
      constraints.one(info.packFraction)
      constraints.nullType(info.type)
    }

    fun newVar(n: VariableDeclarationNode, assertions: NodeAssertions) {
      val ref = getDirectRef(n)
      newVar(assertions.postThen[ref])
      if (assertions.postThen !== assertions.postElse) {
        newVar(assertions.postElse[ref])
      }
    }

    fun noSideEffects(result: NodeAssertions) {
      constraints.noSideEffects(result)
    }

    fun onlySideEffect(result: NodeAssertions, except: Set<Reference>) {
      // TODO expand "except" set with the fields
      constraints.onlyEffects(result, except)
    }

    fun newValue(node: Node, assertions: NodeAssertions, type: MungoType) {
      // TODO full permission to fields...

      val thenInfo = getInfo(node, assertions.postThen)
      val elseInfo = getInfo(node, assertions.postElse)

      constraints.subtype(type, thenInfo.type)
      constraints.one(thenInfo.packFraction)
      if (thenInfo !== elseInfo) {
        constraints.subtype(type, elseInfo.type)
        constraints.one(elseInfo.packFraction)
      }
    }

    fun type(node: Node, assertions: NodeAssertions, type: MungoType) {
      val thenInfo = getInfo(node, assertions.postThen)
      val elseInfo = getInfo(node, assertions.postElse)

      constraints.subtype(type, thenInfo.type)
      if (thenInfo !== elseInfo) {
        constraints.subtype(type, elseInfo.type)
      }
    }
  }

  fun visitInitialAssertion(ast: UnderlyingAST, pre: SymbolicAssertion) {
    pre.forEach { ref, info ->
      when (ref) {
        is ParameterVariable -> {
          constraints.one(info.fraction)
          constraints.paramAndLocalVars(pre, ref, ref.toLocalVariable())
        }
        is LocalVariable -> {
          if (ref.element.getKind() == ElementKind.PARAMETER) {
            constraints.one(info.fraction)
          }
        }
        is ThisReference -> {
          constraints.one(info.fraction)
          constraints.subtype(MungoObjectType.SINGLETON, info.type)
        }
        is FieldAccess -> {
        }
        is ClassName -> {
        }
        is ReturnSpecialVar -> {
          ensures.newVar(info)
        }
        is OldSpecialVar -> {
          ensures.newVar(info)
        }
        is NodeRef -> {

        }
      }
    }
    // TODO lambdas

    if (ast is UnderlyingAST.CFGMethod) {
      for ((a, b) in pre.skeleton.equalities) {
        if (a !is ParameterVariable && b !is ParameterVariable) {
          constraints.notEquality(pre, a, b)
        }
      }
    }
  }

  override fun visitThisLiteral(n: ThisLiteralNode, result: NodeAssertions): Void? {
    require.read(n, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitLocalVariable(n: LocalVariableNode, result: NodeAssertions): Void? {
    require.read(n, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitFieldAccess(n: FieldAccessNode, result: NodeAssertions): Void? {
    require.read(n, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitMethodAccess(n: MethodAccessNode, result: NodeAssertions): Void? {
    require.read(n.receiver, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitVariableDeclaration(n: VariableDeclarationNode, result: NodeAssertions): Void? {
    ensures.newVar(n, result)
    ensures.onlySideEffect(result, setOf(getDirectRef(n)))
    // FIXME nothing equals this variable!
    return null
  }

  /*private fun assign(target: Node, expr: Node, oldRef: OldSpecialVar?, result: NodeAssertions) {
    require.write(target, result)
    require.read(expr, result)

    val targetRef = getDirectRef(target)
    val exprRef = getRef(expr)

    // Permission to the target and expression remain the same
    handle(result) { tail, heads ->
      constraints.same(tail[targetRef].fraction, heads.map { it[targetRef].fraction })
      constraints.same(tail[exprRef].fraction, heads.map { it[exprRef].fraction })
    }

    // Move permissions and type of the old object to the ghost variable
    if (oldRef != null) {
      constraints.transfer(false, result, oldRef, targetRef)
    }

    // Equality
    if (exprRef is NodeRef) {
      constraints.transfer(true, result, targetRef, exprRef)
    } else {
      constraints.equality(result, oldRef, targetRef, exprRef)
    }

    val effects = if (oldRef == null) {
      setOf(targetRef, exprRef)
    } else {
      setOf(targetRef, exprRef, oldRef)
    }
    ensures.onlySideEffect(result, effects)

    constraints.other { setup ->
      val exprs = mutableListOf<BoolExpr>()
      handle(result) { tail, heads ->
        // old = target;
        // target = expr;

        // (P[E/x] <=> replace x with E)
        // {P[E/x]} x := E {P}

        // {P[expr/target][target/old]}
        // old := target
        // {P[expr/target]}
        // target := expr
        // {P}

        // TODO use this logic more!

        // Replace "x" with "e" in "p"
        fun r1(p: Reference, x: Reference, e: Reference) =
          if (p == x) e else p

        fun r2(p: Reference) = if (oldRef == null) {
          r1(p, targetRef, exprRef)
        } else {
          r1(r1(p, targetRef, exprRef), oldRef, targetRef)
        }

        val equalities = tail.skeleton.equalities

        for ((a, b) in equalities) {
          if (effects.contains(a) || effects.contains(b)) {
            val c = r2(a)
            val d = r2(b)
            exprs.add(when {
              c == d -> setup.mkEquals(tail, a, b)
              equalities.contains(Pair(c, d)) -> setup.ctx.mkEq(
                setup.mkEquals(tail, a, b),
                setup.mkAnd(heads.map {
                  setup.mkEquals(it, c, d)
                })
              )
              else -> setup.ctx.mkNot(setup.mkEquals(tail, a, b))
            })
          }
        }
      }
      setup.mkAnd(exprs)
    }
  }*/

  override fun visitAssignment(n: AssignmentNode, result: NodeAssertions): Void? {
    require.write(n.target, result)
    require.read(n.expression, result)

    val targetRef = getDirectRef(n.target)
    val exprRef = getRef(n.expression)
    constraints.equality(result, inferrer.getOldReference(n), targetRef, exprRef)
    return null
  }

  override fun visitReturn(n: ReturnNode, result: NodeAssertions): Void? {
    val expr = n.result
    if (expr == null) {
      ensures.noSideEffects(result)
    } else {
      require.write(n, result)
      require.read(expr, result)

      val targetRef = getDirectRef(n)
      val exprRef = getRef(expr)
      constraints.equality(result, null, targetRef, exprRef)
    }
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: NodeAssertions): Void? {
    val constructor = TreeUtils.elementFromUse(node.tree!!) as Symbol.MethodSymbol
    call(node, null, node.arguments, constructor, result)
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: NodeAssertions): Void? {
    call(n, n.target.receiver, n.arguments, n.target.method as Symbol.MethodSymbol, result)
    return null
  }

  private fun isObjectConstructor(method: ExecutableElement): Boolean {
    if (method.kind == ElementKind.CONSTRUCTOR && method.simpleName.toString() == "<init>") {
      // java.lang.Object constructor is side effect free
      return true
    }
    return false
  }

  private fun call(call: Node, receiver: Node?, argNodes: Collection<Node>, method: Symbol.MethodSymbol, result: NodeAssertions) {
    if (isObjectConstructor(method)) {
      ensures.noSideEffects(result)
      return
    }

    // Is this a constructor call?
    val isConstructor = method.getKind() == ElementKind.CONSTRUCTOR
    // Gather all parameters
    val parameters = inferrer.locationsGatherer.getParameterLocations(method).filter {
      if (isConstructor) it is ParameterVariable else it is ThisReference || it is ParameterVariable
    }
    // Is "this" one of the parameters?
    val includeThis = parameters.any { it is ThisReference }
    // Gather all arguments
    val arguments = mutableListOf<Node>().let {
      if (includeThis && receiver != null) {
        it.add(receiver)
      }
      it.addAll(argNodes)
      it
    }.map { getRef(it) }

    // assert(parameters.size == argExprs.size)

    ensures.onlySideEffect(result, arguments.toSet().plus(getRef(call)))

    // TODO handle methods for which we do not have the code...
    val pre = inferrer.getMethodPre(method) ?: return
    val (postThen, postElse) = inferrer.getMethodPost(method) ?: return

    // Arguments
    var itParams = parameters.iterator()
    var itArgs = arguments.iterator()
    while (itParams.hasNext()) {
      val param = itParams.next()
      val expr = itArgs.next()
      constraints.passingParameter(result.preThen[expr], pre[param])
      if (result.preThen !== result.preElse) {
        constraints.passingParameter(result.preElse[expr], pre[param])
      }
    }

    if (isConstructor) {
      // Constructor return value
      val newType = MungoTypecheck.objectCreation(inferrer.utils, call.type)
      ensures.newValue(call, result, newType)
    } else {
      // Required and ensured states
      if (receiver != null) {
        require.read(receiver, result)

        val graph = inferrer.utils.classUtils.visitClassTypeMirror(receiver.type)
        if (graph == null) {
          // TODO same type
        } else {
          val states = MungoTypecheck.available(inferrer.utils, graph, method)
          val union = MungoUnionType.create(states)
          val destination = MungoTypecheck.refine(inferrer.utils, union, method) { _ -> true }
          // TODO improve computing of destination (e.g. create a Z3 function that takes a type, etc...)
          require.type(receiver, result, union)
          ensures.type(receiver, result, destination)
        }
      }

      // Transfer return value
      if (method.returnType.kind != TypeKind.VOID) {
        constraints.transfer(
          false,
          NodeAssertions(postThen, postElse, result.postThen, result.postElse),
          getRef(call),
          ReturnSpecialVar(call.type)
        )
      }
    }

    // Other effects
    itParams = parameters.iterator()
    itArgs = arguments.iterator()
    while (itParams.hasNext()) {
      val param = itParams.next()
      val expr = itArgs.next()
      // TODO add the fractions that were left in the current context
      constraints.restoringParameter(postThen[param], result.postThen[expr])
      constraints.restoringParameter(postElse[param], result.postElse[expr])
    }

    // TODO equalities from inside the method that can be tracked outside!
  }

  override fun visitTypeCast(n: TypeCastNode, result: NodeAssertions): Void? {
    require.read(n.operand, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitClassName(n: ClassNameNode, result: NodeAssertions): Void? {
    require.read(n, result)
    ensures.noSideEffects(result)
    return null
  }

  override fun visitValueLiteral(n: ValueLiteralNode, result: NodeAssertions): Void? {
    ensures.noSideEffects(result)
    when (n) {
      is NullLiteralNode -> ensures.newValue(n, result, MungoNullType.SINGLETON)
      is StringLiteralNode -> ensures.newValue(n, result, MungoNoProtocolType.SINGLETON)
      else -> ensures.newValue(n, result, MungoPrimitiveType.SINGLETON)
    }
    return null
  }

  override fun visitNode(n: Node?, result: NodeAssertions): Void? {
    if (n != null) {
      println("----")
      println("NOT ANALYZED")
      println(n)
      println(n::class.java)
      println("----")
    }
    return null
  }
}
