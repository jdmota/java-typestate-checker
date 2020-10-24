package org.checkerframework.checker.mungo.assertions

import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.typecheck.*
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.*
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
      onlySideEffect(result, emptySet())
    }

    fun onlySideEffect(result: NodeAssertions, except: Set<Reference>) {
      constraints.onlyEffects(result.preThen, result.postThen, except)
      if (result.preThen !== result.preElse || result.postThen !== result.postElse) {
        constraints.onlyEffects(result.preElse, result.postElse, except)
      }
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

    // TODO What about lambdas???
    for ((a, b) in pre.skeleton.equalities) {
      if (a !is ParameterVariable && b !is ParameterVariable) {
        constraints.notEquality(pre, a, b)
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
    return null
  }

  // TODO handle primitives
  private fun assign(target: Node, expr: Node, oldRef: OldSpecialVar?, result: NodeAssertions) {
    val targetRef = getDirectRef(target)
    val exprRef = getRef(expr)

    fun helper(pre: SymbolicAssertion, post: SymbolicAssertion) {
      val preTargetInfo = pre[targetRef]
      val preExprInfo = getInfo(expr, pre)
      val postTargetInfo = post[targetRef]
      val postExprInfo = getInfo(expr, post)

      // Permission to the target and expression remain the same
      constraints.same(preTargetInfo.fraction, postTargetInfo.fraction)
      constraints.same(preExprInfo.fraction, postExprInfo.fraction)

      if (oldRef != null) {
        val postOldVarInfo = post[oldRef]
        // Move permissions and type of the old object to the ghost variable
        constraints.transfer(target = postOldVarInfo, null, data = preTargetInfo)
      }

      // Equality
      // TODO if then != else, this might be too restrictive...
      if (exprRef is NodeRef) {
        constraints.transfer(target = postTargetInfo, expr = postExprInfo, data = preExprInfo)
      } else {
        constraints.equality(assertion = post, target = targetRef, expr = exprRef, data = preExprInfo)
      }
    }

    helper(result.preThen, result.postThen)
    if (result.preThen !== result.preElse || result.postThen !== result.postElse) {
      helper(result.preElse, result.postElse)
    }

    ensures.onlySideEffect(result, setOf(targetRef, exprRef))
  }

  override fun visitAssignment(n: AssignmentNode, result: NodeAssertions): Void? {
    require.write(n.target, result)
    require.read(n.expression, result)
    assign(n.target, n.expression, inferrer.getOldReference(n), result)
    return null
  }

  override fun visitObjectCreation(node: ObjectCreationNode, result: NodeAssertions): Void? {
    val newType = MungoTypecheck.objectCreation(inferrer.utils, node.type)
    ensures.newValue(node, result, newType)
    return null
  }

  private fun isConstructor(method: ExecutableElement): Boolean {
    if (method.kind == ElementKind.CONSTRUCTOR && method.simpleName.toString() == "<init>") {
      // java.lang.Object constructor is side effect free
      return true
    }
    return false
  }

  /*
  Think of method calls like:

  d = method(a, b, c)

  as:

  #arg0 = a
  #arg1 = b
  #arg2 = c
  method()
  d = #ret
  */
  override fun visitMethodInvocation(n: MethodInvocationNode, result: NodeAssertions): Void? {
    val method = n.target.method as Symbol.MethodSymbol
    if (isConstructor(method)) {
      ensures.noSideEffects(result)
      return null
    }

    require.read(n.target.receiver, result)

    val parameters = inferrer.locationsGatherer.getParameterLocations(method).filter {
      it is ThisReference || it is ParameterVariable
    }
    val includeThis = parameters.any { it is ThisReference }
    val arguments = mutableListOf<Node>().let {
      if (includeThis) it.add(n.target.receiver)
      it.addAll(n.arguments)
      it
    }.map { getRef(it) }

    // assert(parameters.size == argExprs.size)

    println(method)
    println(arguments)
    println(parameters)
    println()

    ensures.onlySideEffect(result, arguments.toSet())

    // TODO handle methods for which we do not have the code...
    val pre = inferrer.getMethodPre(method) ?: return null
    val (postThen, postElse) = inferrer.getMethodPost(method) ?: return null

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

    // Required and ensured states
    val graph = inferrer.utils.classUtils.visitClassTypeMirror(n.target.receiver.type)
    if (graph == null) {
      // TODO same type
    } else {
      val states = MungoTypecheck.available(inferrer.utils, graph, method)
      val union = MungoUnionType.create(states)
      val destination = MungoTypecheck.refine(inferrer.utils, union, method) { _ -> true }
      require.type(n.target.receiver, result, union)
      ensures.type(n.target.receiver, result, destination)
      println("\n$method: $union -> $destination\n")
    }

    // Transfer return value
    if (method.returnType.kind != TypeKind.VOID) {
      // Transfer information about the return value
      // TODO if then != else, this might be too restrictive...
      constraints.transfer(target = getInfo(n, result.postThen), null, data = postThen[ReturnSpecialVar(n.type)])
      if (result.postThen !== result.postElse || postThen !== postElse) {
        constraints.transfer(target = getInfo(n, result.postElse), null, data = postElse[ReturnSpecialVar(n.type)])
      }
    }

    // Other effects
    itParams = parameters.iterator()
    itArgs = arguments.iterator()
    while (itParams.hasNext()) {
      val param = itParams.next()
      val expr = itArgs.next()
      constraints.restoringParameter(postThen[param], result.postThen[expr])
      constraints.restoringParameter(postElse[param], result.postElse[expr])
    }
    return null
  }

  override fun visitReturn(n: ReturnNode, result: NodeAssertions): Void? {
    val expr = n.result
    if (expr == null) {
      ensures.noSideEffects(result)
    } else {
      require.read(expr, result)
      assign(n, expr, null, result)
    }
    return null
  }

  override fun visitTernaryExpression(n: TernaryExpressionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitConditionalNot(n: ConditionalNotNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitEqualTo(n: EqualToNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitNotEqual(n: NotEqualNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitLambdaResultExpression(n: LambdaResultExpressionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitStringConcatenateAssignment(n: StringConcatenateAssignmentNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitCase(n: CaseNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitInstanceOf(n: InstanceOfNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitNarrowingConversion(n: NarrowingConversionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitWideningConversion(n: WideningConversionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitStringConversion(n: StringConversionNode, result: NodeAssertions): Void? {
    return null
  }

  override fun visitTypeCast(n: TypeCastNode, result: NodeAssertions): Void? {
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
    return null
  }
}
