package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.MungoStore
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.common.basetype.BaseTypeVisitor
import org.checkerframework.dataflow.cfg.node.LocalVariableNode
import org.checkerframework.framework.source.Result
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.TreeUtils
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
        checker.report(
          Result.failure(errorKey, constructorTypeMirror, superCall, superTypeMirror),
          superCall)
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
          val receiverValue = typeFactory.getInferredValueFor(receiverTree)
          val checks = MungoTypecheck.check(c.utils, visitorState.path, receiverValue, node, element)
          if (!checks) {
            // Ignore this method invocation tree to avoid (method.invocation.invalid) errors produced by Checker
            skipMethods[node] = true
          }
        }
      }

      // Returned objects must be assigned so that they complete the protocol
      val parent = visitorState.path.parentPath.leaf
      if (parent !is VariableTree && parent !is AssignmentTree) {
        val returnValue = typeFactory.getInferredValueFor(node)
        if (returnValue != null && !returnValue.info.isSubtype(MungoUnionType.create(acceptedFinalTypes))) {
          c.utils.err("Returned object did not complete its protocol", node)
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

    val leftValue: MungoValue? = typeFactory.getStoreBefore(left)?.getValue(LocalVariableNode(left))
    val rightValue: MungoValue? = typeFactory.getInferredValueFor(right)

    if (leftValue == null || rightValue == null) {
      return
    }

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
      return
    }

    // Assignments checks should use the inferred type information
    typeFactory.replaceWithInferredInfo(valueTree, valueType)
    super.commonAssignmentCheck(varType, valueType, valueTree, errorKey)
  }

  override fun visitMemberSelect(node: MemberSelectTree, p: Void?): Void? {
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

  override fun visitIdentifier(node: IdentifierTree, p: Void?): Void? {
    super.visitIdentifier(node, p)

    val element = TreeUtils.elementFromTree(node) as? Symbol.VarSymbol ?: return p

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
        c.utils.err("Object did not complete its protocol", key.element)
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
        c.utils.err("Object did not complete its protocol", key.field)
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

}
