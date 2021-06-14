package jatyc.assertions

import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import jatyc.utils.JTCUtils
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.dataflow.cfg.node.*
import org.checkerframework.javacutil.TreeUtils
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement

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
      type(node, assertions, JTCObjectType.SINGLETON)
    }

    fun type(node: Node, assertions: NodeAssertions, type: JTCType) {
      val thenInfo = getInfo(node, assertions.preThen)
      val elseInfo = getInfo(node, assertions.preElse)

      constraints.subtype(thenInfo.type, type)
      if (thenInfo !== elseInfo) {
        constraints.subtype(elseInfo.type, type)
      }
    }
  }

  private val ensures = object {
    fun noSideEffects(result: NodeAssertions) {
      constraints.noSideEffects(result)
    }
  }

  fun visitInitialAssertion(ast: UnderlyingAST, pre: SymbolicAssertion) {
    if (ast is UnderlyingAST.CFGLambda) {
      // TODO
      return
    }

    if (ast is UnderlyingAST.CFGStatement) {
      // TODO
      return
    }

    val isConstructor = inferrer.isConstructor(ast)
    val isPure = !isConstructor && inferrer.isPure(ast)

    val isReadableMethod = isPure && run {
      val method = ((ast as UnderlyingAST.CFGMethod).method as JCTree.JCMethodDecl).sym
      val receiverType = method.enclosingElement.asType()

      val graph = inferrer.utils.classUtils.visitClassTypeMirror(receiverType)
      if (graph != null) {
        // If this method always leaves the object in the same state
        TypecheckUtils.available(inferrer.utils, graph, method).all {
          it == TypecheckUtils.refine(inferrer.utils, it, method) { true }
        }
      } else {
        false
      }
    }

    fun newUnknown(info: SymbolicInfo) {
      constraints.same(info.fraction, 0)
      constraints.same(info.packFraction, 0)
      constraints.same(info.type, JTCUnknownType.SINGLETON)
      info.forEach { _, childInfo ->
        newUnknown(childInfo)
      }
    }

    fun newVar(info: SymbolicInfo, type: JTCType = JTCUnknownType.SINGLETON) {
      constraints.same(info.fraction, 1)
      constraints.same(info.packFraction, if (type.isSubtype(JTCObjectType.SINGLETON)) 1 else 0)
      constraints.same(info.type, type)
      info.forEach { _, childInfo ->
        newUnknown(childInfo)
      }
      // For now, packed permissions of primitives is zero.
      // This is important so that we do not need to worry about the transferring of those permissions
      // in a way that preserves well-formedness,
      // together with the fact that the implementation does not track equalities between variables/fields that store primitives.
      // For example, what would happen is that the fraction permission would get transferred, but the packed permissions would not,
      // breaking the well-formedness properties (i.e. if fraction is zero, packed fraction needs to be zero),
      // raising a contradiction in the constraints and making the problem unsat.
    }

    pre.forEach { ref, info ->
      when (ref) {
        is ParameterVariable -> {
          constraints.one(info.fraction)
          constraints.paramAndLocalVars(pre, ref, ref.toLocalVariable())
        }
        is LocalVariable -> {
          if (ref.element.getKind() == ElementKind.PARAMETER) {
            constraints.one(info.fraction)
          } else {
            newUnknown(info)
          }
        }
        is ThisReference -> {
          constraints.one(info.fraction)
          constraints.same(info.type, JTCObjectType.SINGLETON)
          if (isReadableMethod) {
            constraints.notZero(info.packFraction)
            constraints.notOne(info.packFraction)
          } else {
            constraints.one(info.packFraction)
          }
        }
        is FieldAccess -> {
          if (isConstructor && ref.isThisField()) {
            constraints.one(info.fraction)
          } else if (isPure) {
            // Force pure methods to require less fractions
            // So that more information can be preserved after this method call
            constraints.notOne(info.fraction)
            constraints.notOne(info.packFraction)
          }
        }
        is ReturnSpecialVar -> {
          newVar(info)
        }
        is OldSpecialVar -> {
          newVar(info)
        }
        is NodeRef -> {
          val node = ref.node
          val type = if (node is ValueLiteralNode) {
            when (node) {
              is NullLiteralNode -> JTCNullType.SINGLETON
              is StringLiteralNode -> JTCNoProtocolType.SINGLETON
              else -> JTCPrimitiveType.SINGLETON
            }
          } else {
            JTCUnknownType.SINGLETON
          }
          newVar(info, type)
        }
        is ClassName -> {
        }
        is OuterContextRef -> {
        }
        is UnknownRef -> {
        }
      }
    }

    for ((a, b) in pre.skeleton.allEqualities) {
      if (a is ParameterVariable && b == a.toLocalVariable()) {
        // Preserve equality
      } else if (b is ParameterVariable && a == b.toLocalVariable()) {
        // Preserve equality
      } else {
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
    constraints.newVariable(result, getDirectRef(n), JTCUnknownType.SINGLETON)
    return null
  }

  private val localVarToThread = mutableMapOf<Reference, LambdaThread>()

  override fun visitAssignment(n: AssignmentNode, result: NodeAssertions): Void? {
    require.write(n.target, result)
    require.read(n.expression, result)

    val targetRef = getDirectRef(n.target)
    val exprRef = getRef(n.expression)
    constraints.equality(result, inferrer.getOldReference(n), targetRef, exprRef)

    // TODO the type of this assignment is the type of the expression

    val lambdaThread = inferrer.analyzeMaybeThreadCreation(n.expression)
    if (lambdaThread != null) {
      // TODO this is totally an hack...
      localVarToThread[targetRef] = lambdaThread
    }
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
    val lambdaThread = inferrer.analyzeMaybeThreadCreation(node)
    if (lambdaThread != null) {
      callForThreads(lambdaThread, node, null, constructor, result)
    } else {
      call(node, null, node.arguments, constructor, result)
    }
    return null
  }

  override fun visitMethodInvocation(n: MethodInvocationNode, result: NodeAssertions): Void? {
    val method = n.target.method as Symbol.MethodSymbol
    val lambdaThread = localVarToThread[getRef(n.target.receiver)]
    if (lambdaThread != null) {
      callForThreads(lambdaThread, n, n.target.receiver, method, result)
    } else {
      call(n, n.target.receiver, n.arguments, method, result)
    }
    return null
  }

  private fun isObjectConstructor(method: ExecutableElement): Boolean {
    if (
      method.kind == ElementKind.CONSTRUCTOR &&
      method.simpleName.toString() == "<init>" &&
      method.enclosingElement.toString() == "java.lang.Object"
    ) {
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

    // TODO handle methods for which we do not have the code...
    val pre = inferrer.getMethodPre(method) ?: return
    val (postThen, postElse) = inferrer.getMethodPost(method) ?: return

    // Is this a constructor call?
    val isConstructor = method.getKind() == ElementKind.CONSTRUCTOR
    // Gather all parameters
    val parameters = inferrer.locationsGatherer.getParameterLocationsForCall(method)
    val parameterFields = parameters.map { inferrer.locationsGatherer.getLocations(it) }
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
    val argumentFields = arguments.map { inferrer.locationsGatherer.getLocations(it) }

    // assert(parameters.size == argExprs.size)

    var typeAfterCall: TypeAfterCall? = null

    if (isConstructor) {
      val objType = method.enclosingElement.asType()
      typeAfterCall = TypeAfterCallSpecific(TypecheckUtils.objectCreation(inferrer.utils, objType))
    } else {
      // Required and ensured states
      if (receiver != null) {
        require.read(receiver, result)

        val graph = inferrer.utils.classUtils.visitClassTypeMirror(receiver.type)
        if (graph != null) {
          val states = TypecheckUtils.available(inferrer.utils, graph, method)
          val union = JTCUnionType.create(states)
          require.type(receiver, result, union)
          typeAfterCall = TypeAfterCallTransition(inferrer.utils, states, method)
        }
      }
    }

    constraints.call(
      result,
      getRef(call),
      receiver?.let { getRef(it) },
      typeAfterCall,
      argumentFields,
      parameterFields,
      methodPre = pre,
      methodPost = setOf(postThen, postElse)
    )
  }

  private fun callForThreads(lambdaThread: LambdaThread, call: Node, receiver: Node?, method: Symbol.MethodSymbol, result: NodeAssertions) {
    val methodName = method.simpleName.toString()
    val isConstructor = method.getKind() == ElementKind.CONSTRUCTOR
    val receiverRef = receiver?.let { getRef(it) }
    val callRef = getRef(call)
    val pre = inferrer.getTreePre(lambdaThread.lambda)
    val posts = inferrer.getTreePost(lambdaThread.lambda).let { setOf(it.first, it.second) }

    fun usedInLambda(ref: Reference) = pre.skeleton.locations.contains(ref)

    fun preconditionToCall(receiverRef: Reference, requiredType: JTCType) {
      constraints.other { c ->
        val pres = setOf(result.preThen, result.preElse)

        ConstraintsSet(c).addIn1(
          Make.S.gt(
            Make.S.min(pres.map { it[receiverRef].fraction.expr }),
            Make.ZERO
          )
        ).addIn1(
          Make.S.eq(
            Make.S.min(pres.map { it[receiverRef].packFraction.expr }),
            Make.ONE
          )
        ).addIn2(
          Make.S.subtype(
            Make.S.union(pres.map { it[receiverRef].type.expr }),
            Make.S.type(requiredType)
          )
        )
      }
    }

    when (methodName) {
      "start" -> {
        val requiredType = JTCUnionType.create(TypecheckUtils.available(inferrer.utils, lambdaThread.graph, method))
        val ensuredType = TypecheckUtils.refine(inferrer.utils, requiredType, method) { true }
        preconditionToCall(receiverRef!!, requiredType)

        constraints.other { c ->
          val set = ConstraintsSet(c)

          fun helper(from: SymbolicInfo, to: SymbolicInfo) {
            set.addIn1(Make.S.ge(from.fraction.expr, to.fraction.expr))
            set.addIn1(Make.S.ge(from.packFraction.expr, to.packFraction.expr))
            set.addIn2(Make.S.subtype(from.type.expr, to.type.expr))
            /*from.children.forEach { (ref, info) ->
              helper(info, to.children[ref.replace(from.ref, to.ref)]!!)
            }*/
          }

          for (head in setOf(result.preThen, result.preElse)) {
            head.forEach { ref, info ->
              if (usedInLambda(ref)) {
                helper(info, pre[ref])
              }
            }
          }
          set
        }

        constraints.other { c ->
          reduce(ConstraintsSet(c), result) { set, tail, heads, choice ->
            tail.forEach { ref, info ->
              if (usedInLambda(ref)) {
                set.addIn1(Make.S.eq(
                  info.fraction.expr,
                  Make.S.sub(
                    Make.S.min(heads.map { it[ref].fraction.expr }),
                    pre[ref].fraction.expr
                  )
                ))

                set.addIn1(Make.S.eq(
                  info.packFraction.expr,
                  Make.S.sub(
                    Make.S.min(heads.map { it[ref].packFraction.expr }),
                    pre[ref].packFraction.expr
                  )
                ))

                set.addIn2(Make.S.eq(
                  info.type.expr,
                  Make.S.ite(
                    Make.S.and(listOf(Make.S.gt(info.fraction.expr, Make.ZERO), Make.S.gt(info.packFraction.expr, Make.ZERO))),
                    Make.S.union(heads.map { it[ref].type.expr }),
                    Make.UNKNOWN
                  )
                ))
              } else {
                set.addIn1(Make.S.eq(
                  info.fraction.expr,
                  Make.S.min(heads.map { it[ref].fraction.expr }))
                )

                set.addIn1(Make.S.eq(
                  info.packFraction.expr,
                  Make.S.min(heads.map { it[ref].packFraction.expr }))
                )

                if (ref == receiverRef) {
                  set.addIn2(Make.S.eq(
                    info.type.expr,
                    Make.S.type(ensuredType)
                  ))
                } else {
                  set.addIn2(Make.S.eq(
                    info.type.expr,
                    Make.S.union(heads.map { it[ref].type.expr })
                  ))
                }
              }
            }

            // FIXME
            for ((a, b) in tail.skeleton.allEqualities) {
              set.addIn1(
                Make.S.eq(
                  Make.S.equals(tail, a, b),
                  Make.S.mult(heads.map { Make.S.equals(it, a, b) })
                )
              )
            }
          }
        }
      }
      "join" -> {
        val requiredType = JTCUnionType.create(TypecheckUtils.available(inferrer.utils, lambdaThread.graph, method))
        val ensuredType = TypecheckUtils.refine(inferrer.utils, requiredType, method) { true }
        preconditionToCall(receiverRef!!, requiredType)

        constraints.other { c ->
          reduce(ConstraintsSet(c), result) { set, tail, heads, choice ->
            tail.forEach { ref, info ->
              if (usedInLambda(ref)) {
                set.addIn1(Make.S.eq(
                  info.fraction.expr,
                  Make.S.add(listOf(
                    Make.S.min(heads.map { it[ref].fraction.expr }),
                    Make.S.min(posts.map { it[ref].fraction.expr })
                  ))
                ))

                set.addIn1(Make.S.eq(
                  info.packFraction.expr,
                  Make.S.add(listOf(
                    Make.S.min(heads.map { it[ref].packFraction.expr }),
                    Make.S.min(posts.map { it[ref].packFraction.expr })
                  ))
                ))

                set.addIn2(Make.S.eq(
                  info.type.expr,
                  Make.S.ite(
                    Make.S.and(listOf(Make.S.gt(info.fraction.expr, Make.ZERO), Make.S.gt(info.packFraction.expr, Make.ZERO))),
                    Make.S.intersection(heads.plus(posts).map { it[ref].type.expr }),
                    Make.UNKNOWN
                  )
                ))
              } else {
                set.addIn1(Make.S.eq(
                  info.fraction.expr,
                  Make.S.min(heads.map { it[ref].fraction.expr }))
                )

                set.addIn1(Make.S.eq(
                  info.packFraction.expr,
                  Make.S.min(heads.map { it[ref].packFraction.expr }))
                )

                if (ref == receiverRef) {
                  set.addIn2(Make.S.eq(
                    info.type.expr,
                    Make.S.type(ensuredType)
                  ))
                } else {
                  set.addIn2(Make.S.eq(
                    info.type.expr,
                    Make.S.union(heads.map { it[ref].type.expr })
                  ))
                }
              }
            }

            // FIXME
            for ((a, b) in tail.skeleton.allEqualities) {
              set.addIn1(
                Make.S.eq(
                  Make.S.equals(tail, a, b),
                  Make.S.mult(heads.map { Make.S.equals(it, a, b) })
                )
              )
            }
          }
        }
      }
      else -> {
        constraints.other { c ->
          reduce(ConstraintsSet(c), result) { set, tail, heads, choice ->
            tail.forEach { ref, info ->
              if (ref == callRef && isConstructor) {
                set.addIn1(Make.S.eq(info.fraction.expr, Make.ONE))
                set.addIn1(Make.S.eq(info.packFraction.expr, Make.ONE))
                set.addIn2(Make.S.eq(
                  info.type.expr,
                  Make.S.type(
                    JTCStateType.create(lambdaThread.graph, lambdaThread.graph.getInitialState())
                  )
                ))
              } else {
                set.addIn1(Make.S.eq(
                  info.fraction.expr,
                  Make.S.min(heads.map { it[ref].fraction.expr }))
                )
                set.addIn1(Make.S.eq(
                  info.packFraction.expr,
                  Make.S.min(heads.map { it[ref].packFraction.expr }))
                )
                set.addIn2(Make.S.eq(
                  info.type.expr,
                  Make.S.union(heads.map { it[ref].type.expr })
                ))
              }
            }

            for ((a, b) in tail.skeleton.allEqualities) {
              set.addIn1(
                Make.S.eq(
                  Make.S.equals(tail, a, b),
                  Make.S.mult(heads.map { Make.S.equals(it, a, b) })
                )
              )
            }
          }
        }
      }
    }
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
    return null
  }

  override fun visitMemberReference(n: FunctionalInterfaceNode, result: NodeAssertions): Void? {
    ensures.noSideEffects(result)
    return null
  }

  override fun visitConditionalNot(n: ConditionalNotNode, result: NodeAssertions): Void? {
    constraints.implies(result.preThen, result.postElse)
    constraints.implies(result.preElse, result.postThen)
    return null
  }

  private fun getBooleanValue(node: Node): Boolean? = when (node) {
    is BooleanLiteralNode -> node.value!!
    is ConditionalNotNode -> getBooleanValue(node.operand)?.not()
    else -> null
  }

  private fun getLabel(node: Node) = when (node) {
    is FieldAccessNode -> if (JTCUtils.isEnum(node.type)) node.fieldName else null
    else -> getBooleanValue(node)?.let { if (it) "true" else "false" }
  }

  override fun visitEqualTo(n: EqualToNode, result: NodeAssertions): Void? {
    val left = n.leftOperand
    val right = n.rightOperand
    val label = getLabel(right)
    if (left is MethodInvocationNode && label != null) {
      val receiver = left.target.receiver
      val method = left.target.method
      if (receiver != null && method is Symbol.MethodSymbol) {
        val graph = inferrer.utils.classUtils.visitClassTypeMirror(receiver.type)
        if (graph != null) {
          val preStates = TypecheckUtils.available(inferrer.utils, graph, method)
          // TODO improve this to be more precise
          val thenType = TypecheckUtils.refine(inferrer.utils, JTCUnionType.create(preStates), method) { it == label }
          val elseType = TypecheckUtils.refine(inferrer.utils, JTCUnionType.create(preStates), method) { it != label }
          constraints.refinedType(result, getRef(receiver), thenType, elseType)
          return null
        }
      }
    }
    ensures.noSideEffects(result)
    return null
  }

  override fun visitNode(n: Node?, result: NodeAssertions): Void? {
    if (n != null) {
      /*println("----")
      println("NOT ANALYZED")
      println(n)
      println(n::class.java)
      println("----")*/
      ensures.noSideEffects(result)
    }
    return null
  }
}
