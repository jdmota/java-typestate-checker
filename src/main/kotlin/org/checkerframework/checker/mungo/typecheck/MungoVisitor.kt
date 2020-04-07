package org.checkerframework.checker.mungo.typecheck

import com.sun.source.tree.*
import com.sun.tools.javac.code.Symbol
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.MungoStore
import org.checkerframework.checker.mungo.analysis.MungoValue
import org.checkerframework.checker.mungo.annotators.MungoAnnotatedTypeFactory
import org.checkerframework.common.basetype.BaseTypeVisitor
import org.checkerframework.dataflow.cfg.node.LocalVariableNode
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import javax.lang.model.element.ElementKind

class MungoVisitor(checker: MungoChecker) : BaseTypeVisitor<MungoAnnotatedTypeFactory>(checker) {

  private val c = checker

  override fun createTypeFactory(): MungoAnnotatedTypeFactory {
    // Pass "checker" and not "c" because "c" is initialized after "super()" and "createTypeFactory()"...
    return MungoAnnotatedTypeFactory(checker as MungoChecker)
  }

  // TODO visit all annotations to make sure @MungoTypestate only appears in class/interfaces??
  // TODO what if another class points to the same protocol file?? error? or fine? avoid duplicate processing

  private fun checkOwnCall(node: MethodInvocationTree, element: Symbol.MethodSymbol): Boolean {
    if (TreeUtils.isSelfAccess(node) && !element.isStatic && !element.isStaticOrInstanceInit && !element.isPrivate) {
      val hasProtocol = c.utils.visitClassSymbol(element.enclosingElement) != null
      if (hasProtocol) {
        c.utils.err("Cannot call its own public method", node)
        return false
      }
    }
    return true // It's fine. Proceed checking.
  }

  override fun visitMethodInvocation(node: MethodInvocationTree, p: Void?): Void? {
    val element = TreeUtils.elementFromUse(node)
    if (element is Symbol.MethodSymbol && element.getKind() == ElementKind.METHOD && checkOwnCall(node, element)) {
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

    return super.visitMethodInvocation(node, p)
  }

  private val skipMethods = WeakIdentityHashMap<MethodInvocationTree, Boolean>()

  override fun skipReceiverSubtypeCheck(node: MethodInvocationTree, methodDefinitionReceiver: AnnotatedTypeMirror, methodCallReceiver: AnnotatedTypeMirror): Boolean {
    return skipMethods.contains(node) || super.skipReceiverSubtypeCheck(node, methodDefinitionReceiver, methodCallReceiver)
  }

  private val acceptedFinalTypes = listOf(MungoNullType.SINGLETON, MungoMovedType.SINGLETON, MungoEndedType.SINGLETON, MungoNoProtocolType.SINGLETON)

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
    if (valueTree is IdentifierTree && valueTree.name.toString() == "this") {
      val element = TreeUtils.elementFromTree(valueTree)
      if (element != null) {
        val hasProtocol = c.utils.visitClassSymbol(element.enclosingElement) != null
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
