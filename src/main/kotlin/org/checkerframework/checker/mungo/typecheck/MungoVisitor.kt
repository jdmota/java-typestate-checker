package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.TreeInfo
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.MungoStore
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.utils.ClassUtils
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.common.basetype.BaseTypeVisitor
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.dataflow.cfg.node.LocalVariableNode
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.AnnotationUtils
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement

class MungoVisitor(checker: MungoChecker) : BaseTypeVisitor<MungoAnnotatedTypeFactory>(checker) {

  private val c = checker
  private val utils get() = c.utils

  override fun createTypeFactory(): MungoAnnotatedTypeFactory {
    // Pass "checker" and not "c" because "c" is initialized after "super()" and "createTypeFactory()"...
    return MungoAnnotatedTypeFactory(checker as MungoChecker)
  }

  private fun returnTypeAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree) {
    if (parent is MethodTree && parent.modifiers.annotations.contains(node)) {
      val typeMirror = TreeUtils.elementFromTree(parent.returnType)?.asType()
      if (typeMirror != null) {
        if (ClassUtils.isJavaLangObject(typeMirror)) {
          utils.err("@MungoState has no meaning in Object type", node)
        } else {
          val graph = c.utils.classUtils.visitClassTypeMirror(typeMirror)
          if (graph == null) {
            utils.err("@MungoState has no meaning since this type has no protocol", node)
          } else {
            val stateNames = MungoUtils.getAnnotationValue(annoMirror)
            utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
          }
        }
      }
    } else {
      utils.err("@MungoState should only be used on return types", node)
    }
  }

  private fun checkParameterAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree, parentParent: Tree, name: String) {
    if (parent is VariableTree && parentParent is MethodTree && parentParent.parameters.contains(parent)) {
      val typeMirror = TreeUtils.elementFromTree(parent)?.asType()
      if (typeMirror != null) {
        if (ClassUtils.isJavaLangObject(typeMirror)) {
          utils.err("@$name has no meaning in Object type", node)
        } else {
          val graph = c.utils.classUtils.visitClassTypeMirror(typeMirror)
          if (graph == null) {
            utils.err("@$name has no meaning since this type has no protocol", node)
          } else {
            val stateNames = MungoUtils.getAnnotationValue(annoMirror)
            utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
          }
        }
      }
    } else {
      utils.err("@$name should only be used in method parameters", node)
    }
  }

  override fun visitAnnotation(node: AnnotationTree, p: Void?): Void? {
    super.visitAnnotation(node, p)

    val annoMirror = TreeUtils.annotationFromAnnotationTree(node)
    val parent = visitorState.path.parentPath.parentPath.leaf
    val parentParent = visitorState.path.parentPath.parentPath.parentPath.leaf

    when (AnnotationUtils.annotationName(annoMirror)) {
      MungoUtils.mungoState -> returnTypeAnnotation(node, annoMirror, parent)
      MungoUtils.mungoRequires -> checkParameterAnnotation(node, annoMirror, parent, parentParent, "MungoRequires")
      MungoUtils.mungoEnsures -> checkParameterAnnotation(node, annoMirror, parent, parentParent, "MungoEnsures")
    }

    // TODO visit all annotations to make sure @MungoTypestate only appears in classes

    return null
  }

  override fun checkThisOrSuperConstructorCall(superCall: MethodInvocationTree, errorKey: @CompilerMessageKey String) {
    // Override this method so that Checker does not report super.invocation.invalid
    // The change was introduced because of https://github.com/typetools/checker-framework/issues/2264
    val enclosingMethod = TreeUtils.enclosingMethod(atypeFactory.getPath(superCall))
    val superType = atypeFactory.getAnnotatedType(superCall)
    val constructorType = atypeFactory.getAnnotatedType(enclosingMethod)
    val topAnnotations = atypeFactory.qualifierHierarchy.topAnnotations
    for (topAnno in topAnnotations) {
      val superTypeMirror = superType.getAnnotationInHierarchy(topAnno)
      val constructorTypeMirror = constructorType.returnType.getAnnotationInHierarchy(topAnno)
      // Invert here
      // TODO understand why the authors check the opposite...
      if (!atypeFactory.qualifierHierarchy.isSubtype(constructorTypeMirror, superTypeMirror)) {
        checker.reportError(superCall, errorKey, constructorTypeMirror, superCall, superTypeMirror)
      }
    }
  }

  override fun checkConstructorResult(constructorType: AnnotatedTypeMirror.AnnotatedExecutableType, constructorElement: ExecutableElement) {
    // Do not report inconsistent.constructor.type warning
    // TODO understand why the result type of the constructor not being top is a problem...
  }

  private fun checkOwnCall(node: MethodInvocationTree, element: Symbol.MethodSymbol): Boolean {
    if (TreeUtils.isSelfAccess(node) && !element.isStatic && !element.isStaticOrInstanceInit && !element.isPrivate) {
      val hasProtocol = utils.classUtils.visitClassSymbol(element.enclosingElement) != null
      if (hasProtocol) {
        utils.err("Cannot call its own public method", node)
        return false
      }
    }
    return true // It's fine. Proceed checking.
  }

  override fun visitMethodInvocation(node: MethodInvocationTree, p: Void?): Void? {
    val element = TreeUtils.elementFromUse(node)

    if (element is Symbol.MethodSymbol && element.getKind() == ElementKind.METHOD) {

      if (checkOwnCall(node, element)) {
        val receiverTree = TreeUtils.getReceiverTree(node)
        if (receiverTree != null) {
          val type = typeFactory.getTypeFor(receiverTree)
          val checks = MungoTypecheck.check(utils, type, node, element)
          if (!checks) {
            // Ignore this method invocation tree to avoid (method.invocation.invalid) errors produced by Checker
            skipMethods[node] = true
          }
        }
      }

      // Returned objects must be assigned so that they complete the protocol
      val parent = visitorState.path.parentPath.leaf
      if (parent !is VariableTree && parent !is AssignmentTree) {
        val type = typeFactory.getTypeFor(node)
        if (!MungoTypecheck.canDrop(type)) {
          utils.err("Returned object did not complete its protocol. Type: ${type.format()}", node)
        }
      }

    }

    if (ElementUtils.isElementFromByteCode(element)) {
      for (arg in node.arguments) {
        val type = typeFactory.getTypeFor(arg)
        if (!type.isSubtype(MungoTypecheck.noProtocolTypes)) {
          utils.err("Passing an object with protocol to a method that cannot be analyzed", arg)
        }
      }
    }

    return super.visitMethodInvocation(node, p)
  }

  private val skipMethods = WeakIdentityHashMap<MethodInvocationTree, Boolean>()

  override fun skipReceiverSubtypeCheck(node: MethodInvocationTree, methodDefinitionReceiver: AnnotatedTypeMirror, methodCallReceiver: AnnotatedTypeMirror): Boolean {
    return skipMethods.contains(node) || super.skipReceiverSubtypeCheck(node, methodDefinitionReceiver, methodCallReceiver)
  }

  private fun getParamTypesAfterCall(parameters: List<VariableTree>): Map<String, MungoType?> {
    return parameters.map {
      val typeMirror = TreeUtils.elementFromTree(it)!!.asType()
      val type = MungoTypecheck.typeAfterMethodCall(utils, typeMirror)
      Pair(it.name.toString(), type)
    }.toMap()
  }

  private fun checkFinalType(name: String, value: MungoValue, tree: Tree) {
    val errorPrefix = if (tree is VariableTree) "Object" else "Cannot override because object"

    // Even if there is a @MungoEnsures in the enclosing method,
    // we should always check completion for example if there are assignments inside a loop,
    // which might create other references different from the one in the parameter.
    if (!MungoTypecheck.canDrop(value.info)) {
      utils.err("$errorPrefix has not ended its protocol. Type: ${value.info.format()}", tree)
    }

    val parameters = when (val method = TreeUtils.enclosingMethodOrLambda(visitorState.path)) {
      is MethodTree -> method.parameters
      is LambdaExpressionTree -> method.parameters
      else -> listOf()
    }
    val types = getParamTypesAfterCall(parameters)
    val finalType = types[name]

    if (finalType != null) {
      if (!value.info.isSubtype(finalType)) {
        utils.err("$errorPrefix is not in the state specified by @MungoEnsures. Type: ${value.info.format()}", tree)
      }
    }
  }

  override fun commonAssignmentCheck(left: Tree, right: ExpressionTree, errorKey: String?) {
    super.commonAssignmentCheck(left, right, errorKey)

    when (left) {
      is VariableTree -> {
        // In case we are in a loop, ensure the object from the previous loop has completed its protocol
        val leftValue = typeFactory.getStoreBefore(left)?.getValueIfTracked(LocalVariableNode(left)) ?: return
        checkFinalType(left.name.toString(), leftValue, left)
      }
      is ExpressionTree -> {
        val receiver = FlowExpressions.internalReprOf(typeFactory, left)
        val leftValue = typeFactory.getStoreBefore(left)?.getValue(receiver) ?: return

        checkFinalType(receiver.toString(), leftValue, left)

        if (left is JCTree.JCFieldAccess) {
          if (ElementUtils.isElementFromByteCode(left.selected.type.asElement())) {
            val type = typeFactory.getTypeFor(right)
            if (!type.isSubtype(MungoTypecheck.noProtocolTypes)) {
              utils.err("Assigning an object with protocol to a field that cannot be analyzed", left)
            }
          }
        }
      }
    }
  }

  override fun commonAssignmentCheck(varType: AnnotatedTypeMirror, valueType: AnnotatedTypeMirror, valueTree: Tree, errorKey: String?) {
    // Detect possible leaked "this"
    if (valueTree is ExpressionTree && TreeUtils.isExplicitThisDereference(valueTree)) {
      val element = TreeUtils.elementFromTree(valueTree)
      if (element != null) {
        val hasProtocol = utils.classUtils.visitClassSymbol(element.enclosingElement) != null
        if (hasProtocol) {
          utils.err("Possible 'this' leak", valueTree)
          return
        }
      }
    }

    if (TypesUtils.isPrimitive(varType.underlyingType) && TypesUtils.isBoxedPrimitive(valueType.underlyingType)) {
      if (!checkForNullability(valueType, valueTree, UNBOXING_OF_NULLABLE)) {
        // Only issue the unboxing of nullable error
        return
      }
    }

    // Assignments from boxed primitives to primitives and vice-versa should be allowed
    val varMungoType = atypeFactory.getTypeFor(varType)
    val valMungoType = atypeFactory.getTypeFor(valueTree, valueType)
    if (isPrimitiveAndBoxedPrimitive(varMungoType, valMungoType, valueType)) return
    if (isPrimitiveAndBoxedPrimitive(valMungoType, varMungoType, varType)) return

    super.commonAssignmentCheck(varType, valueType, valueTree, errorKey)
  }

  private fun isPrimitiveAndBoxedPrimitive(aType: MungoType, bType: MungoType, bMirror: AnnotatedTypeMirror) =
    aType.isSubtype(MungoPrimitiveType.SINGLETON) && bType.isSubtype(MungoNoProtocolType.SINGLETON) && TypesUtils.isBoxedPrimitive(bMirror.underlyingType)

  override fun visitMemberSelect(node: MemberSelectTree, p: Void?): Void? {
    super.visitMemberSelect(node, p)

    val element = TreeUtils.elementFromTree(node) ?: return p

    // Check this field access if this is not a self access, or static access, or method call
    if (!(TreeUtils.isExplicitThisDereference(node)
        || TreeUtils.isSelfAccess(node)
        || node.expression.kind == Tree.Kind.PARAMETERIZED_TYPE
        || ElementUtils.isStatic(element))) {
      val parent = atypeFactory.getPath(node).parentPath.leaf
      if (!(parent is MethodInvocationTree && parent.methodSelect === node)) {
        val typeInfo = typeFactory.getTypeFor(node.expression)
        MungoTypecheck.checkFieldAccess(utils, typeInfo, node)
      }
    }

    // See if it has protocol
    utils.classUtils.visitClassOfElement(element) ?: return p

    // If "this"...
    if (TreeUtils.isExplicitThisDereference(node)) {
      val enclosingMethodOrLambda = MungoUtils.enclosingMethodOrLambda(visitorState.path) ?: return p
      if (enclosingMethodOrLambda.leaf.kind == Tree.Kind.LAMBDA_EXPRESSION) {
        utils.err("$node was moved to a different closure", node)
      }
    }

    return p
  }

  override fun visitMemberReference(node: MemberReferenceTree, p: Void?): Void? {
    val expr = node.qualifierExpression
    val type = typeFactory.getTypeFor(expr)
    if (!type.isSubtype(MungoTypecheck.noProtocolTypes)) {
      utils.err("Cannot create reference for method of an object with protocol", node)
    }

    return super.visitMemberReference(node, p)
  }

  private fun printTypeInfo(node: IdentifierTree) {
    if (c.shouldReportTypeInfo() && !node.name.contentEquals("this")) {
      val annotatedType = typeFactory.getAnnotatedType(node)
      if (annotatedType != null) {
        val type = MungoUtils.mungoTypeFromAnnotations(annotatedType.annotations)
        if (type !is MungoNoProtocolType && type !is MungoPrimitiveType) {
          c.reportWarning(node, "$node: ${type.format()}")
        }
      }
    }
  }

  override fun visitIdentifier(node: IdentifierTree, p: Void?): Void? {
    super.visitIdentifier(node, p)

    val element = TreeUtils.elementFromTree(node) as? Symbol.VarSymbol ?: return p

    // Print type information for testing purposes
    printTypeInfo(node)

    if (utils.wasMovedToDiffClosure(visitorState.path, node, element)) {
      utils.err("$node was moved to a different closure", node)
    }

    return p
  }

  private fun ensureLocalCompleteness(parameters: List<VariableTree>, exitStore: MungoStore) {
    val paramTypes = getParamTypesAfterCall(parameters)

    // Make sure protocols of local variables complete
    for ((key, value) in exitStore.iterateOverLocalVars()) {
      val typeAfterCall = paramTypes[key.toString()]

      if (typeAfterCall == null) {
        if (!MungoTypecheck.canDrop(value.info)) {
          utils.err("Object did not complete its protocol. Type: ${value.info.format()}", key.element)
        }
      } else {
        if (!value.info.isSubtype(typeAfterCall)) {
          utils.err("Final type does not match what was specified by @MungoEnsures. Type: ${value.info.format()}", key.element)
        }
      }
    }
  }

  override fun visitMethod(node: MethodTree, p: Void?): Void? {
    typeFactory.getRegularExitStore(node)?.let { ensureLocalCompleteness(node.parameters, it) }
    return super.visitMethod(node, p)
  }

  override fun visitLambdaExpression(node: LambdaExpressionTree, p: Void?): Void? {
    typeFactory.getRegularExitStore(node.body)?.let { ensureLocalCompleteness(node.parameters, it) }
    return super.visitLambdaExpression(node, p)
  }

  private fun ensureFieldsCompleteness(exitStore: MungoStore) {
    // Make sure protocols of fields complete
    for ((key, value) in exitStore.iterateOverFields()) {
      if (!MungoTypecheck.canDrop(value.info)) {
        utils.err("Object did not complete its protocol. Type: ${value.info.format()}", key.field)
      }
    }
  }

  override fun processClassTree(classTree: ClassTree) {
    super.processClassTree(classTree)

    typeFactory.getStatesToStore(classTree)?.let {
      for ((state, store) in it) {
        if (state.canEndHere()) {
          ensureFieldsCompleteness(store)
        }
      }
    }

    typeFactory.getGlobalStore(classTree)?.let {
      ensureFieldsCompleteness(it)
    }
  }

  // Nullness checks
  // Adapted from https://github.com/typetools/checker-framework/blob/master/checker/src/main/java/org/checkerframework/checker/nullness/NullnessVisitor.java
  // TODO check redundant tests
  // TODO check arrays of non-null items are initialized

  /** Case 2: Check for implicit `.iterator` call.  */
  override fun visitEnhancedForLoop(node: EnhancedForLoopTree, p: Void?): Void? {
    checkForNullability(node.expression, ITERATING_NULLABLE)
    return super.visitEnhancedForLoop(node, p)
  }

  /** Case 3: Check for array dereferencing.  */
  override fun visitArrayAccess(node: ArrayAccessTree, p: Void?): Void? {
    checkForNullability(node.expression, ACCESSING_NULLABLE)
    return super.visitArrayAccess(node, p)
  }

  /** Case 4: Check for thrown exception nullness.  */
  override fun checkThrownExpression(node: ThrowTree) {
    checkForNullability(node.expression, THROWING_NULLABLE)
  }

  /** Case 5: Check for synchronizing locks.  */
  override fun visitSynchronized(node: SynchronizedTree, p: Void?): Void? {
    checkForNullability(node.expression, LOCKING_NULLABLE)
    return super.visitSynchronized(node, p)
  }

  override fun visitIf(node: IfTree, p: Void?): Void? {
    checkForNullability(node.condition, CONDITION_NULLABLE)
    return super.visitIf(node, p)
  }

  /** Case 6: Check for redundant nullness tests Case 7: unboxing case: primitive operations.  */
  override fun visitBinary(node: BinaryTree, p: Void?): Void? {
    val leftOp = node.leftOperand
    val rightOp = node.rightOperand
    if (isUnboxingOperation(node)) {
      checkForNullability(leftOp, UNBOXING_OF_NULLABLE)
      checkForNullability(rightOp, UNBOXING_OF_NULLABLE)
    }
    return super.visitBinary(node, p)
  }

  /** Case 7: unboxing case: primitive operation.  */
  override fun visitUnary(node: UnaryTree, p: Void?): Void? {
    checkForNullability(node.expression, UNBOXING_OF_NULLABLE)
    return super.visitUnary(node, p)
  }

  /** Case 7: unboxing case: primitive operation.  */
  override fun visitCompoundAssignment(node: CompoundAssignmentTree, p: Void?): Void? {
    // ignore String concatenation
    if (!isString(node)) {
      checkForNullability(node.variable, UNBOXING_OF_NULLABLE)
      checkForNullability(node.expression, UNBOXING_OF_NULLABLE)
    }
    return super.visitCompoundAssignment(node, p)
  }

  /** Case 7: unboxing case: casting to a primitive.  */
  override fun visitTypeCast(node: TypeCastTree, p: Void?): Void? {
    if (isPrimitive(node) && !isPrimitive(node.expression)) {
      if (!checkForNullability(node.expression, UNBOXING_OF_NULLABLE)) {
        // If unboxing of nullable is issued, don't issue any other errors.
        return null
      }
    }
    return super.visitTypeCast(node, p)
  }

  override fun visitSwitch(node: SwitchTree, p: Void?): Void? {
    checkForNullability(node.expression, SWITCHING_NULLABLE)
    return super.visitSwitch(node, p)
  }

  override fun visitForLoop(node: ForLoopTree, p: Void?): Void? {
    if (node.condition != null) {
      // Condition is null e.g. in "for (;;) {...}"
      checkForNullability(node.condition, CONDITION_NULLABLE)
    }
    return super.visitForLoop(node, p)
  }

  override fun visitWhileLoop(node: WhileLoopTree, p: Void?): Void? {
    checkForNullability(node.condition, CONDITION_NULLABLE)
    return super.visitWhileLoop(node, p)
  }

  override fun visitDoWhileLoop(node: DoWhileLoopTree, p: Void?): Void? {
    checkForNullability(node.condition, CONDITION_NULLABLE)
    return super.visitDoWhileLoop(node, p)
  }

  override fun visitConditionalExpression(node: ConditionalExpressionTree, p: Void?): Void? {
    checkForNullability(node.condition, CONDITION_NULLABLE)
    return super.visitConditionalExpression(node, p)
  }

  override fun checkExceptionParameter(node: CatchTree) {
    // BaseTypeVisitor forces annotations on exception parameters to be top,
    // but because exceptions can never be null, the Nullness Checker
    // does not require this check.
  }

  /////////////// Utility methods ///////////////
  /**
   * Issues the error message if the type of the tree is subtype of MungoNullType
   *
   * @param tree the tree where the error is to reported
   * @param errMsg the error message (must be [CompilerMessageKey])
   * @return whether or not the check succeeded
   */
  private fun checkForNullability(tree: ExpressionTree, errMsg: @CompilerMessageKey String): Boolean {
    return checkForNullability(typeFactory.getAnnotatedType(tree), tree, errMsg)
  }

  /**
   * Issues the error message if an expression with this type may be null.
   *
   * @param type annotated type
   * @param tree the tree where the error is to reported
   * @param errMsg the error message (must be [CompilerMessageKey])
   * @return whether or not the check succeeded
   */
  private fun checkForNullability(type: AnnotatedTypeMirror, tree: Tree, errMsg: @CompilerMessageKey String): Boolean {
    val inferred = typeFactory.getTypeFor(tree, type)
    return if (MungoNullType.SINGLETON.isSubtype(inferred)) {
      c.reportError(tree, errMsg, tree)
      false
    } else true
  }

  /** @return true if binary operation could cause an unboxing operation
   */
  private fun isUnboxingOperation(tree: BinaryTree): Boolean {
    return if (tree.kind == Tree.Kind.EQUAL_TO || tree.kind == Tree.Kind.NOT_EQUAL_TO) {
      // it is valid to check equality between two reference types, even
      // if one (or both) of them is null
      isPrimitive(tree.leftOperand) != isPrimitive(tree.rightOperand)
    } else {
      // All BinaryTree's are of type String, a primitive type or the
      // reference type equivalent of a primitive type. Furthermore,
      // Strings don't have a primitive type, and therefore only
      // BinaryTrees that aren't String can cause unboxing.
      !isString(tree)
    }
  }

  private val stringType = elements.getTypeElement("java.lang.String").asType()

  /** @return true if the type of the tree is a super of String
   */
  private fun isString(tree: ExpressionTree): Boolean {
    val type = TreeUtils.typeOf(tree)
    return types.isAssignable(stringType, type)
  }

  companion object {
    // Error message keys
    private const val UNBOXING_OF_NULLABLE: @CompilerMessageKey String = "unboxing.of.nullable"
    private const val LOCKING_NULLABLE: @CompilerMessageKey String = "locking.nullable"
    private const val THROWING_NULLABLE: @CompilerMessageKey String = "throwing.nullable"
    private const val ACCESSING_NULLABLE: @CompilerMessageKey String = "accessing.nullable"
    private const val CONDITION_NULLABLE: @CompilerMessageKey String = "condition.nullable"
    private const val ITERATING_NULLABLE: @CompilerMessageKey String = "iterating.over.nullable"
    private const val SWITCHING_NULLABLE: @CompilerMessageKey String = "switching.nullable"
    private const val DEREFERENCE_OF_NULLABLE: @CompilerMessageKey String = "dereference.of.nullable"

    private fun isPrimitive(tree: ExpressionTree) = TreeUtils.typeOf(tree).kind.isPrimitive
  }

}
