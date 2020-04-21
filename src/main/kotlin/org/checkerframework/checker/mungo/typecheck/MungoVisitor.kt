package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.MungoStore
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.common.basetype.BaseTypeVisitor
import org.checkerframework.dataflow.analysis.FlowExpressions
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import javax.lang.model.element.ElementKind
import javax.lang.model.element.ExecutableElement

class MungoVisitor(checker: MungoChecker) : BaseTypeVisitor<MungoAnnotatedTypeFactory>(checker) {

  private val c = checker

  override fun createTypeFactory(): MungoAnnotatedTypeFactory {
    // Pass "checker" and not "c" because "c" is initialized after "super()" and "createTypeFactory()"...
    return MungoAnnotatedTypeFactory(checker as MungoChecker)
  }

  // TODO visit all annotations to make sure @MungoTypestate only appears in class/interfaces??
  // TODO what if another class points to the same protocol file?? error? or fine? avoid duplicate processing

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
      val hasProtocol = c.utils.classUtils.visitClassSymbol(element.enclosingElement) != null
      if (hasProtocol) {
        c.utils.err("Cannot call its own public method", node)
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
          val checks = MungoTypecheck.check(c.utils, visitorState.path, type, node, element)
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
        if (!type.isSubtype(MungoUnionType.create(acceptedFinalTypes))) {
          c.utils.err("Returned object did not complete its protocol. Type: ${type.format()}", node)
        }
      }

    }

    return super.visitMethodInvocation(node, p)
  }

  private val skipMethods = WeakIdentityHashMap<MethodInvocationTree, Boolean>()

  override fun skipReceiverSubtypeCheck(node: MethodInvocationTree, methodDefinitionReceiver: AnnotatedTypeMirror, methodCallReceiver: AnnotatedTypeMirror): Boolean {
    return skipMethods.contains(node) || super.skipReceiverSubtypeCheck(node, methodDefinitionReceiver, methodCallReceiver)
  }

  private val acceptedFinalTypes = listOf(MungoPrimitiveType.SINGLETON, MungoNullType.SINGLETON, MungoMovedType.SINGLETON, MungoEndedType.SINGLETON, MungoNoProtocolType.SINGLETON)

  override fun commonAssignmentCheck(left: Tree, right: ExpressionTree, errorKey: String?) {
    super.commonAssignmentCheck(left, right, errorKey)

    if (left is VariableTree) {
      // Since we adapted MungoStore#leastUpperBound,
      // now, while analyzing loops,
      // the store includes information from the previous loop.
      // Ignore variable declarations
      // so that they are not considered as overrides.
      return
    }

    if (left !is ExpressionTree) return

    val receiver = FlowExpressions.internalReprOf(typeFactory, left)
    val leftValue = typeFactory.getStoreBefore(left)?.getValue(receiver) ?: return

    // Only allow overrides on null, ended, moved object, or object without protocol
    if (!leftValue.info.isSubtype(MungoUnionType.create(acceptedFinalTypes))) {
      c.utils.err("Cannot override because object has not ended its protocol", left)
    }
  }

  override fun commonAssignmentCheck(varType: AnnotatedTypeMirror, valueType: AnnotatedTypeMirror, valueTree: Tree, errorKey: String?) {
    // Detect possible leaked "this"
    if (valueTree is ExpressionTree && TreeUtils.isExplicitThisDereference(valueTree)) {
      val element = TreeUtils.elementFromTree(valueTree)
      if (element != null) {
        val hasProtocol = c.utils.classUtils.visitClassSymbol(element.enclosingElement) != null
        if (hasProtocol) {
          c.utils.err("Possible 'this' leak", valueTree)
          return
        }
      }
    }

    if (!nullnessCommonAssignmentCheck(varType, valueType, valueTree)) {
      // Only issue the unboxing of nullable error
      return
    }

    super.commonAssignmentCheck(varType, valueType, valueTree, errorKey)
  }

  override fun visitMemberSelect(node: MemberSelectTree, p: Void?): Void? {
    nullnessVisitMemberSelect(node)
    super.visitMemberSelect(node, p)

    val element = TreeUtils.elementFromTree(node) ?: return p

    // See if it has protocol
    c.utils.classUtils.visitClassOfElement(element) ?: return p

    // If "this"...
    if (TreeUtils.isExplicitThisDereference(node)) {
      val enclosingMethodOrLambda = MungoUtils.enclosingMethodOrLambda(visitorState.path) ?: return p
      if (enclosingMethodOrLambda.leaf.kind == Tree.Kind.LAMBDA_EXPRESSION) {
        c.utils.err("$node was moved to a different closure", node)
      }
    }

    return p
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

    // See if it has protocol
    c.utils.classUtils.visitClassOfElement(element) ?: return p

    // If "this"...
    if (TreeUtils.isExplicitThisDereference(node)) {
      val enclosingMethodOrLambda = MungoUtils.enclosingMethodOrLambda(visitorState.path) ?: return p
      if (enclosingMethodOrLambda.leaf.kind == Tree.Kind.LAMBDA_EXPRESSION) {
        c.utils.err("$node was moved to a different closure", node)
      }
      return p
    }

    // Find declaration and enclosing method/lambda
    val declarationTree = typeFactory.declarationFromElement(element) ?: return p
    val declaration = c.treeUtils.getPath(visitorState.path.compilationUnit, declarationTree) ?: return p
    val enclosingMethodOrLambda = MungoUtils.enclosingMethodOrLambda(visitorState.path) ?: return p

    // See if variable declaration is enclosed in the enclosing method or lambda or not
    var path1: TreePath? = declaration
    var path2: TreePath? = enclosingMethodOrLambda
    while (path1 != null && path2 != null && path1 != enclosingMethodOrLambda) {
      path1 = path1.parentPath
      path2 = path2.parentPath
    }

    // Error if:
    // 1. Declaration is closer to the root (path1 == null && path2 != null)
    // 2. Both are at the same level (path1 == null && path2 == null) and identifier is enclosed in a lambda
    if (path1 == null && (path2 != null || enclosingMethodOrLambda.leaf.kind == Tree.Kind.LAMBDA_EXPRESSION)) {
      c.utils.err("${node.name} was moved to a different closure", node)
    }

    return p
  }

  private fun ensureLocalCompleteness(exitStore: MungoStore) {
    // Make sure protocols of local variables complete
    for ((key, value) in exitStore.iterateOverLocalVars()) {
      if (!value.info.isSubtype(MungoUnionType.create(acceptedFinalTypes))) {
        c.utils.err("Object did not complete its protocol. Type: ${value.info.format()}", key.element)
      }
    }
  }

  override fun visitMethod(node: MethodTree, p: Void?): Void? {
    typeFactory.getRegularExitStore(node)?.let { ensureLocalCompleteness(it) }
    return super.visitMethod(node, p)
  }

  override fun visitLambdaExpression(node: LambdaExpressionTree, p: Void?): Void? {
    typeFactory.getRegularExitStore(node.body)?.let { ensureLocalCompleteness(it) }
    return super.visitLambdaExpression(node, p)
  }

  private fun ensureFieldsCompleteness(exitStore: MungoStore) {
    // Make sure protocols of fields complete
    for ((key, value) in exitStore.iterateOverFields()) {
      if (!value.info.isSubtype(MungoUnionType.create(acceptedFinalTypes))) {
        c.utils.err("Object did not complete its protocol. Type: ${value.info.format()}", key.field)
      }
    }
  }

  override fun processClassTree(classTree: ClassTree) {
    super.processClassTree(classTree)

    val statesToStore = typeFactory.getStatesToStore(classTree) ?: return

    for ((state, store) in statesToStore) {
      if (state.transitions.isEmpty()) {
        ensureFieldsCompleteness(store)
      }
    }
  }

  // Nullness checks
  // Adapted from https://github.com/typetools/checker-framework/blob/master/checker/src/main/java/org/checkerframework/checker/nullness/NullnessVisitor.java
  // TODO check redundant tests
  // TODO check arrays of non-null items are initialized

  private fun nullnessCommonAssignmentCheck(varType: AnnotatedTypeMirror, valueType: AnnotatedTypeMirror, valueTree: Tree): Boolean {
    if (TypesUtils.isPrimitive(varType.underlyingType) && !TypesUtils.isPrimitive(valueType.underlyingType)) {
      return checkForNullability(valueType, valueTree, UNBOXING_OF_NULLABLE)
    }
    return true
  }

  /** Case 1: Check for null dereferencing.  */
  private fun nullnessVisitMemberSelect(node: MemberSelectTree) {
    val parent = visitorState.path.parentPath.leaf
    if (parent is MethodInvocationTree && parent.methodSelect === node) {
      // No need to check nullness if we are in a method invocation
      return
    }

    val e = TreeUtils.elementFromTree(node)
    if (!(TreeUtils.isSelfAccess(node)
        || node.expression.kind == Tree.Kind.PARAMETERIZED_TYPE // case 8. static member access
        || ElementUtils.isStatic(e))) {
      checkForNullability(node.expression, DEREFERENCE_OF_NULLABLE)
    }
  }

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
