package jatyc.core.linearmode

import com.sun.source.tree.CompilationUnitTree
import com.sun.source.tree.Tree
import com.sun.tools.javac.code.Type
import jatyc.JavaTypestateChecker
import jatyc.core.*
import jatyc.core.cfg.*

class Inference(
  private val cfChecker: JavaTypestateChecker,
  private val hierarchy: JavaTypesHierarchy,
  private val typeIntroducer: TypeIntroducer,
  private val typecheckUtils: TypecheckUtils,
  private val inference: LinearModeInference,
  private val classAnalysis: LinearModeClassAnalysis
) {

  private val allLabels: (String) -> Boolean = { true }
  private val ifTrue: (String) -> Boolean = { it == "true" }
  private val ifFalse: (String) -> Boolean = { it == "false" }

  fun getRoot(node: AdaptedThing): CompilationUnitTree {
    return node.cfRoot ?: error("no root? $node ${node::class.java}")
  }

  fun getTree(node: AdaptedThing): Tree {
    return node.cfTree ?: node.cfNode?.tree ?: error("no tree? $node ${node::class.java}")
  }

  // TODO improve how we preserve conditional information!

  private fun assign(node: CodeExpr, targetType: JTCType, pre: Store, post: Store, leftRef: Reference, rightRef: Reference) {
    if (node is Assign) {
      post[Reference.old(node)] = pre[leftRef]
    }

    if (leftRef == Reference.returnRef || leftRef.isSwitchVar()) {
      for ((ref, info) in pre) {
        if (info.conditionalOn(rightRef)) {
          post[ref] = info.replaceCondition(leftRef)
        }
      }
    }

    // If this is a normal assignment or the target expects a linear type, move ownership to the target
    // Otherwise, the target gets the shared type and the right expression keeps the linear type
    val move = node is Assign || targetType.requiresLinear()

    val typeToAssign = if (move) pre[rightRef].type else pre[rightRef].type.toShared()
    val typeInExpr = if (move) pre[rightRef].type.toShared() else pre[rightRef].type

    post[leftRef] = typeToAssign.intersect(targetType)
    post[rightRef] = typeInExpr
    post[Reference.make(node)] = pre[rightRef].type.toShared()

    when {
      typeToAssign.isSubtype(targetType) -> inference.errors.remove(node)
      targetType is JTCBottomType -> inference.errors[node] = "Cannot perform assignment because [${leftRef.format()}] is not accessible here"
      else -> inference.errors[node] = when (node) {
        is Assign -> "Cannot perform assignment because ${typeToAssign.format()} is not a subtype of ${targetType.format()}"
        is ParamAssign -> {
          val method = node.call.methodExpr
          val param = method.parameters[node.idx]
          if (param.isThis) {
            "Cannot call [${method.name}] on ${typeToAssign.format()}"
          } else {
            "Incompatible parameter because ${typeToAssign.format()} is not a subtype of ${targetType.format()}"
          }
        }
        is Return -> "Incompatible return value because ${typeToAssign.format()} is not a subtype of ${targetType.format()}"
        else -> "INTERNAL ERROR"
      }
    }
  }

  fun analyzeCode(func: FuncDeclaration, pre: Store, node: CodeExpr, post: Store) {
    val clazz = func.clazz
    val thisRef = Reference.makeThis(func)

    for ((ref, info) in pre) {
      post[ref] = info.toRegular()
    }

    when (node) {
      is VarDeclaration -> {
        val ref = Reference.make(node.id)
        val inLoop = ref in post

        inference.errors.remove(node)
        if (inLoop) {
          val type = post[ref].type
          if (!typecheckUtils.canDrop(type)) {
            inference.errors[node] = "The previous value of [${ref.format()}] did not complete its protocol (found: ${type.format()})"
          }
        }

        post[ref] = JTCNullType.SINGLETON
      }
      is NewObj -> {
        post[Reference.make(node)] = node.type
      }
      is Assign -> {
        val leftRef = Reference.makeFromLHS(node)
        val rightRef = Reference.make(node.right)
        // Do not allow field assignments unless the receiver object is "this" and we have linear access to it
        val targetType = when {
          thisRef != null && leftRef.isFieldOf(thisRef) && pre[thisRef].type.requiresLinear() ->
            clazz!!.allFields(classAnalysis.classes).find { leftRef.isFieldOf(thisRef, it.id) }!!.type
          leftRef.isField() ->
            JTCBottomType.SINGLETON
          else ->
            JTCUnknownType.SINGLETON
        }
        assign(node, targetType, pre, post, leftRef, rightRef)
      }
      is ParamAssign -> {
        val leftRef = Reference.makeFromLHS(node)
        val rightRef = Reference.make(node.expr)
        assign(node, node.call.methodExpr.parameters[node.idx].requires, pre, post, leftRef, rightRef)
      }
      is Return -> {
        if (node.expr == null) {
          post[Reference.returnRef] = JTCNullType.SINGLETON
          post[Reference.make(node)] = JTCNullType.SINGLETON
        } else {
          val leftRef = Reference.returnRef
          val rightRef = Reference.make(node.expr)
          assign(node, node.type, pre, post, leftRef, rightRef)
        }
      }
      is MethodCall -> {
        // Note for later: a call is non-virtual if static or init or super call or private call
        val nodeRef = Reference.make(node)
        val methodExpr = node.methodExpr
        val arguments = node.parameters
        val argsIt = arguments.iterator()

        val parameters = methodExpr.parameters
        val paramsIt = parameters.iterator()

        val isSelfCall = thisRef != null && parameters.isNotEmpty() && parameters.first().isThis && Reference.make(arguments.first().expr) == thisRef

        if (
          isSelfCall &&
          !func.isConstructor && !methodExpr.isConstructor &&
          !methodExpr.isAnytime && methodExpr.isPublic
        ) {
          // We are calling our own public method!
          inference.errors[node] = "Cannot call own public method [${methodExpr.name}]"
          post[nodeRef] = JTCBottomType.SINGLETON
          post.toBottom()
          return
        } else {
          inference.errors.remove(node)
        }

        // We might need to invalidate some information...
        if (!methodExpr.isPure && isSelfCall) {
          checkNotNull(clazz)
          checkNotNull(thisRef)
          // If this is a self call we need to invalidate the information about the fields
          // Remember that we do not allow field accesses unless we are in a method of the object
          // so the only way to modify fields is to perform a self call
          val modified = clazz.allFields(classAnalysis.classes)
          for (field in modified) {
            post[Reference.make(thisRef, field)] = field.type
          }
        }

        // Invariant: arguments.size == parameters.size
        while (argsIt.hasNext()) {
          val arg = argsIt.next()
          val param = paramsIt.next()

          val argRef = Reference.makeFromLHS(arg)
          val exprRef = Reference.make(arg.expr)

          // First we refine the type of the parameter variable
          if (param.isThis) {
            if (methodExpr.name == "<init>") {
              post[argRef] = typecheckUtils.invariant(pre[argRef].type).intersect(param.ensures)
            } else {
              val returnType = methodExpr.returnType
              val returnsBool = returnType.isSubtype(hierarchy.BOOLEAN)
              val returnsEnum = returnType.isSubtype(hierarchy.ENUM)
              val currentType = pre[argRef].type

              when {
                returnsBool -> {
                  post[argRef] = ConditionalStoreInfo(
                    nodeRef,
                    typecheckUtils.refine(currentType, node, ifTrue),
                    typecheckUtils.refine(currentType, node, ifFalse)
                  )
                }
                returnsEnum -> {
                  if (returnType is JTCSharedType) {
                    val (qualifiedName, labels) = returnType.javaType.getEnumLabels()
                    val cases = mutableMapOf<String, JTCType>()
                    for (label in labels) {
                      cases["$qualifiedName.$label"] = typecheckUtils.refine(currentType, node) { it == label }
                    }
                    post[argRef] = CasesStoreInfo(nodeRef, cases)
                  } else {
                    post[argRef] = typecheckUtils.refine(currentType, node, allLabels)
                  }
                }
                else -> {
                  post[argRef] = typecheckUtils.refine(currentType, node, allLabels)
                }
              }

              if (typecheckUtils.check(currentType, node)) {
                inference.errors.remove(node)
              } else {
                inference.errors[node] = "Cannot call [${node.methodExpr.name}] on ${currentType.format()}"
              }
            }
          } else {
            post[argRef] = typecheckUtils.invariant(pre[argRef].type).intersect(param.ensures)
          }

          // Ensure the parameter expression has the ownership
          val argInfo = post[argRef]
          val argType = argInfo.type
          if (argType.requiresLinear()) {
            post[argRef] = argType.toShared()
            post[exprRef] = argInfo // Preserve conditional info!
          }
        }

        // The type of the method call is the type of the return value
        post[nodeRef] = methodExpr.returnType

        // This means that the method interrupts execution
        if (methodExpr.returnType is JTCBottomType) {
          post.toBottom()
        }
      }
      is Id -> {
        // Preserve conditional information
        for ((ref, info) in pre) {
          post[ref] = info
        }

        val currentType = pre[Reference.make(node)].type
        showType(func, node, currentType)

        if (currentType is JTCUnknownType) {
          inference.errors[node] = "Cannot access [${node.name}]"
          post[Reference.make(node)] = JTCBottomType.SINGLETON
        } else {
          inference.errors.remove(node)
        }
      }
      is Select -> {
        // Preserve conditional information
        for ((ref, info) in pre) {
          post[ref] = info
        }

        val ref = Reference.make(node)
        val obj = node.expr
        val objRef = Reference.make(node.expr)
        val objType = pre[objRef].type

        var currentType: JTCType? = null

        if (objType is JTCBottomType || objType is JTCNullType) {
          currentType = JTCBottomType.SINGLETON
        } else if (node.id == "length" && objType is JTCSharedType && objType.javaType.isJavaArray()) {
          currentType = hierarchy.INTEGER
        } else {
          // Handle enums or stuff like java.lang.System.out
          if (obj is SymbolResolveExpr) {
            currentType = typeIntroducer.getEnumFieldType(obj.javaType.original, node.id)
              ?: typeIntroducer.getJDKStaticFieldType(obj.javaType.original, node.id)
          }
          // Or default to what we currently know
          currentType = currentType ?: pre[ref].type
        }

        showType(func, node, currentType)

        when {
          currentType is JTCUnknownType -> {
            inference.errors[node] = "Cannot access [${node.format("")}]"
            post[ref] = JTCBottomType.SINGLETON
          }
          obj !is SymbolResolveExpr && JTCNullType.SINGLETON.isSubtype(objType) -> {
            inference.errors[node] = "Cannot access field [${node.id}] of null"
            post[objRef] = typecheckUtils.refineToNonNull(objType)
            post[ref] = currentType
          }
          else -> {
            inference.errors.remove(node)
            post[ref] = currentType
          }
        }
      }
      is Literal -> {
        // Preserve conditional information
        for ((ref, info) in pre) {
          post[ref] = info
        }

        val nodeRef = Reference.make(node)
        post[nodeRef] = when (node) {
          is BooleanLiteral -> hierarchy.BOOLEAN
          is CharLiteral -> hierarchy.CHAR
          is DoubleLiteral -> hierarchy.DOUBLE
          is FloatLiteral -> hierarchy.FLOAT
          is IntegerLiteral -> hierarchy.INTEGER
          is LongLiteral -> hierarchy.LONG
          is ShortLiteral -> hierarchy.SHORT
          is NullLiteral -> JTCNullType.SINGLETON
          is StringLiteral -> hierarchy.STRING
        }
      }
      is CastExpr -> {
        if (node.type is JTCPrimitiveType) {
          // Casts to primitive values are conversions
          post[Reference.make(node)] = node.type
        } else {
          val exprRef = Reference.make(node.expr)
          val currentType = pre[exprRef].type
          val moreSpecificType = currentType.intersect(node.type)
          post[exprRef] = moreSpecificType

          if (currentType.isSubtype(node.type)) {
            inference.errors.remove(node)
          } else {
            inference.errors[node] = "Unsafe cast"
          }
        }
      }
      is CaseExpr -> {
        // Preserve conditional information
        for ((ref, info) in pre) {
          post[ref] = info
        }

        val value = (node.switchOp as Assign).left
        val test = node.caseOp
        val valueRef = Reference.make(value)
        val nodeRef = Reference.make(node)

        val label = getLabel(test)
        if (label != null) {
          for ((ref, info) in pre) {
            if (info.conditionalOn(valueRef)) {
              post[ref] = ConditionalStoreInfo(nodeRef, info.withLabel(valueRef, label).type, info.withoutLabel(valueRef, label).type)
            }
          }
        }
      }
      is NullCheck -> {
        val exprRef = Reference.make(node.expr)
        val currentType = pre[exprRef].type
        val notNull = typecheckUtils.refineToNonNull(currentType)
        post[exprRef] = notNull

        if (JTCNullType.SINGLETON.isSubtype(currentType)) {
          inference.errors[node] = node.message
        } else {
          inference.errors.remove(node)
        }
      }
      is BinaryExpr -> {
        when (node.operator) {
          BinaryOP.And,
          BinaryOP.Or -> post[Reference.make(node)] = hierarchy.BOOLEAN
          BinaryOP.Equal -> {
            val nodeRef = Reference.make(node)
            val (left, right) = literalOnTheRight(node)
            val leftRef = Reference.make(left)
            val currentType = pre[leftRef].type
            if (right is NullLiteral) {
              post[leftRef] = ConditionalStoreInfo(
                nodeRef,
                typecheckUtils.refineToNull(currentType),
                typecheckUtils.refineToNonNull(currentType)
              )
            } else {
              val label = getLabel(right)
              if (label != null) {
                for ((ref, info) in pre) {
                  if (info.conditionalOn(leftRef)) {
                    post[ref] = ConditionalStoreInfo(nodeRef, info.withLabel(leftRef, label).type, info.withoutLabel(leftRef, label).type)
                  }
                }
              }
            }
            post[nodeRef] = hierarchy.BOOLEAN
          }
          BinaryOP.NotEqual -> {
            val nodeRef = Reference.make(node)
            val (left, right) = literalOnTheRight(node)
            val leftRef = Reference.make(left)
            val currentType = pre[leftRef].type
            if (right is NullLiteral) {
              post[leftRef] = ConditionalStoreInfo(
                nodeRef,
                typecheckUtils.refineToNonNull(currentType),
                typecheckUtils.refineToNull(currentType)
              )
            } else {
              val label = getLabel(right)
              if (label != null) {
                for ((ref, info) in pre) {
                  if (info.conditionalOn(leftRef)) {
                    post[ref] = ConditionalStoreInfo(nodeRef, info.withoutLabel(leftRef, label).type, info.withLabel(leftRef, label).type)
                  }
                }
              }
            }
            post[nodeRef] = hierarchy.BOOLEAN
          }
          BinaryOP.Is -> {
            val nodeRef = Reference.make(node)
            val leftRef = Reference.make(node.left)
            val currentType = pre[leftRef].type
            val rightExpr = node.right as SymbolResolveExpr
            post[leftRef] = ConditionalStoreInfo(
              nodeRef,
              typecheckUtils.refineToNonNull(currentType).intersect(rightExpr.type),
              currentType
            )
            post[nodeRef] = hierarchy.BOOLEAN
          }
          BinaryOP.Add,
          BinaryOP.Sub,
          BinaryOP.Mult,
          BinaryOP.FloatDivision,
          BinaryOP.FloatRemainder,
          BinaryOP.IntDivision,
          BinaryOP.IntRemainder,
          BinaryOP.BitwiseAnd,
          BinaryOP.BitwiseOr,
          BinaryOP.BitwiseXor,
          BinaryOP.LeftShift,
          BinaryOP.SignedRightShift,
          BinaryOP.UnsignedRightShift -> post[Reference.make(node)] = hierarchy.getPrimitive(node.cfType as Type.JCPrimitiveType)
          BinaryOP.GreaterThan,
          BinaryOP.GreaterThanOrEqual,
          BinaryOP.LessThan,
          BinaryOP.LessThanOrEqual -> post[Reference.make(node)] = hierarchy.BOOLEAN
          BinaryOP.StringConcat -> post[Reference.make(node)] = hierarchy.STRING
        }
      }
      is UnaryExpr -> {
        when (node.operator) {
          UnaryOP.Minus,
          UnaryOP.Plus,
          UnaryOP.BitwiseComplement,
          UnaryOP.Widening,
          UnaryOP.Narrowing -> post[Reference.make(node)] = hierarchy.getPrimitive(node.cfType as Type.JCPrimitiveType)
          UnaryOP.Not -> {
            val nodeRef = Reference.make(node)
            val exprRef = Reference.make(node.expr)
            // Reverse stores
            for ((ref, info) in pre) {
              post[ref] = info.not(original = exprRef, negation = nodeRef)
            }
            post[nodeRef] = hierarchy.BOOLEAN
          }
          UnaryOP.ToString -> post[Reference.make(node)] = hierarchy.STRING
        }
      }
      is NewArrayWithDimensions -> {
        inference.errors.remove(node)

        for ((idx, init) in node.dimensions.withIndex()) {
          val valueType = pre[Reference.make(init)].type.toShared()
          if (!valueType.isSubtype(hierarchy.INTEGER)) {
            inference.errors[node] = "Dimension in index $idx with type ${valueType.format()} is not a subtype of ${hierarchy.INTEGER}"
            break
          }
        }

        post[Reference.make(node)] = node.type
      }
      is NewArrayWithValues -> {
        inference.errors.remove(node)

        for ((idx, init) in node.initializers.withIndex()) {
          val valueType = pre[Reference.make(init)].type.toShared()
          if (!valueType.isSubtype(node.componentType)) {
            inference.errors[node] = "Array value in index $idx with type ${valueType.format()} is not a subtype of ${node.componentType.format()}"
            break
          }
        }

        post[Reference.make(node)] = node.type
      }
      is SynchronizedExprEnd -> {
        // TODO
      }
      is SynchronizedExprStart -> {
        // TODO
      }
      is TernaryExpr -> {
        post[Reference.make(node)] = pre[Reference.make(node.thenExpr)].union(pre[Reference.make(node.elseExpr)])
      }
      is ThrowExpr -> {
        post.toBottom()
      }
      is SymbolResolveExpr -> {
        // Preserve conditional information
        for ((ref, info) in pre) {
          post[ref] = info
        }
        // Skip
      }
      is NoOPExpr -> {
        // Preserve conditional information
        for ((ref, info) in pre) {
          post[ref] = info
        }
        // Skip
      }
      is FuncDeclaration -> {
        // We start with an empty store so we do not use variables in outer scopes
        classAnalysis.analyzeMethod(null, node, Store())
      }
      is ClassDecl -> {
        classAnalysis.analyze(node)
      }
      is ClassDeclAndCompanion -> {
        classAnalysis.analyze(node.nonStatic)
        classAnalysis.analyze(node.static)
      }
      is FuncInterface -> {
        // This case should come after FuncDeclaration since FuncDeclaration is a subtype of FuncInterface
        // Skip
      }
    }
  }

  fun analyzeEnd(func: FuncDeclaration, store: Store) {
    val thisRef = Reference.makeThis(func)
    val params = func.parameters.mapNotNull { if (it.ensures.requiresLinear()) Pair(Reference.make(it.id), it.ensures) else null }.toMap()

    val funcErrors = mutableListOf<String>()
    inference.completionErrors[func] = funcErrors

    for ((ref, info) in store) {
      val type = info.type
      if (ref.isFieldOf(thisRef) || params.containsKey(ref) || ref == Reference.returnRef) {
        // We check completion of objects in fields later
        // and we check @Ensure annotations are respected as well
        continue
      }
      if (!typecheckUtils.canDrop(type)) {
        if (ref is OldReference) {
          val leftRef = Reference.make(ref.assign.left)
          inference.completionErrors[ref.assign] = listOf("The previous value of [${leftRef.format()}] did not complete its protocol (found: ${type.format()})")
        } else if (ref is CodeExprReference && ref.code is MethodCall) {
          inference.completionErrors[ref.code] = listOf("Returned value did not complete its protocol (found: ${type.format()})")
        } else {
          funcErrors.add("[${ref.format()}] did not complete its protocol (found: ${type.format()})")
        }
      }
    }

    for ((ref, expected) in params) {
      val actual = store[ref].type
      if (!actual.isSubtype(expected)) {
        funcErrors.add("Type of parameter [${ref.format()}] is ${actual.format()}, expected ${expected.format()}}")
      }
    }
  }

  fun getBooleanValue(node: CodeExpr): Boolean? = when {
    node is BooleanLiteral -> node.value
    node is UnaryExpr && node.operator == UnaryOP.Not -> getBooleanValue(node.expr)?.not()
    else -> null
  }

  private fun isEnumValue(code: CodeExpr): Boolean {
    return code is Select && code.expr is SymbolResolveExpr && code.expr.javaType.isEnum()
  }

  private fun getLabel(code: CodeExpr): String? {
    return if (code is Select && code.expr is SymbolResolveExpr && code.expr.javaType.isEnum()) {
      "${code.expr.qualifiedName}.${code.id}"
    } else if (code is BooleanLiteral) {
      if (code.value) "true" else "false"
    } else null
  }

  private fun literalOnTheRight(binary: BinaryExpr): Pair<CodeExpr, CodeExpr> {
    return if (binary.left is Literal || isEnumValue(binary.left)) {
      Pair(binary.right, binary.left)
    } else {
      Pair(binary.left, binary.right)
    }
  }

  private fun showType(func: FuncDeclaration, node: CodeExpr, currentType: JTCType) {
    if (node is Id && (node.name == "this" || node.name.contains("#"))) {
      return
    }
    if (!cfChecker.shouldReportTypeInfo()) {
      return
    }
    if (currentType is JTCPrimitiveType) {
      return
    }
    val ref = Reference.make(node)
    inference.warnings[node] = listOf("${ref.format()}: ${currentType.format()}")
  }
}
