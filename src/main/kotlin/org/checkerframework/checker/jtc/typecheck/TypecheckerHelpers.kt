package org.checkerframework.checker.jtc.typecheck

import com.sun.source.tree.*
import com.sun.source.util.TreePath
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.code.Type
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.jtc.JavaTypestateChecker
import org.checkerframework.checker.jtc.analysis.*
import org.checkerframework.checker.jtc.utils.ClassUtils
import org.checkerframework.checker.jtc.utils.JTCUtils
import org.checkerframework.checker.jtc.utils.isSelfAccess
import org.checkerframework.framework.source.SourceVisitor
import org.checkerframework.framework.type.AnnotatedTypeMirror
import org.checkerframework.javacutil.ElementUtils
import org.checkerframework.javacutil.TreeUtils
import org.checkerframework.javacutil.TypesUtils
import javax.lang.model.element.AnnotationMirror
import javax.lang.model.element.ExecutableElement
import javax.lang.model.type.TypeMirror

open class TypecheckerHelpers(val checker: JavaTypestateChecker) : SourceVisitor<Void?, Void?>(checker) {

  protected val analyzer = Analyzer(checker)
  protected val utils get() = checker.utils

  protected fun checkReturnTypeAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree) {
    if (parent is MethodTree && parent.modifiers.annotations.contains(node)) {
      val typeMirror = TreeUtils.elementFromTree(parent.returnType)?.asType()
      if (typeMirror != null) {
        if (ClassUtils.isJavaLangObject(typeMirror)) {
          utils.err("@State has no meaning in Object type", node)
        } else {
          val graph = utils.classUtils.visitClassTypeMirror(typeMirror)
          if (graph == null) {
            utils.err("@State has no meaning since this type has no protocol", node)
          } else {
            val stateNames = JTCUtils.getAnnotationValue(annoMirror)
            utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
          }
        }
      }
    } else {
      utils.err("@State should only be used on return types", node)
    }
  }

  protected fun checkParameterAnnotation(node: AnnotationTree, annoMirror: AnnotationMirror, parent: Tree, parentParent: Tree, name: String) {
    if (parent is VariableTree && parentParent is MethodTree && parentParent.parameters.contains(parent)) {
      val typeMirror = TreeUtils.elementFromTree(parent)?.asType()
      if (typeMirror != null) {
        if (ClassUtils.isJavaLangObject(typeMirror)) {
          utils.err("@$name has no meaning in Object type", node)
        } else {
          val graph = utils.classUtils.visitClassTypeMirror(typeMirror)
          if (graph == null) {
            utils.err("@$name has no meaning since this type has no protocol", node)
          } else {
            val stateNames = JTCUtils.getAnnotationValue(annoMirror)
            utils.checkStates(graph, stateNames).forEach { utils.err(it, node) }
          }
        }
      }
    } else {
      utils.err("@$name should only be used in method parameters", node)
    }
  }

  protected fun checkForNullability(tree: ExpressionTree, errMsg: String): Boolean {
    val inferred = analyzer.getInferredType(tree)
    return if (JTCNullType.SINGLETON.isSubtype(inferred)) {
      checker.reportError(tree, errMsg, tree)
      false
    } else true
  }

  protected fun ensureFieldsCompleteness(exitStore: Store) {
    // Make sure protocols of fields complete
    for ((key, value) in exitStore) {
      if (key is FieldAccess && key.isThisField() && !TypecheckUtils.canDrop(value.jtcType)) {
        utils.err("Object did not complete its protocol. Type: ${value.jtcType.format()}", key.field)
      }
    }
  }

  protected fun ensureLocalCompleteness(parameters: List<VariableTree>, exitStore: Store) {
    val paramTypes = getParamTypesAfterCall(parameters)

    // Make sure protocols of local variables complete
    for ((key, value) in exitStore) {
      if (key !is LocalVariable) continue

      val typeAfterCall = paramTypes[key.toString()]

      if (typeAfterCall == null) {
        if (!TypecheckUtils.canDrop(value.jtcType)) {
          utils.err("Object did not complete its protocol. Type: ${value.jtcType.format()}", key.element)
        }
      } else {
        if (!value.jtcType.isSubtype(typeAfterCall)) {
          utils.err("Final type does not match what was specified by @Ensures. Type: ${value.jtcType.format()}", key.element)
        }
      }
    }
  }

  protected fun checkOwnCall(node: MethodInvocationTree, element: Symbol.MethodSymbol): Boolean {
    if (isSelfAccess(node) && !element.isStatic && !element.isStaticOrInstanceInit && !element.isPrivate) {
      val hasProtocol = utils.classUtils.visitClassSymbol(element.enclosingElement) != null
      if (hasProtocol) {
        utils.err("Cannot call its own public method", node)
        return false
      }
    }
    return true // It's fine. Proceed checking.
  }

  private fun getParamTypesAfterCall(parameters: List<VariableTree>): Map<String, JTCType?> {
    return parameters.map {
      val typeMirror = TreeUtils.elementFromTree(it)!!.asType()
      val type = TypecheckUtils.typeAfterMethodCall(utils, typeMirror)
      Pair(it.name.toString(), type)
    }.toMap()
  }

  private fun checkFinalType(name: String, value: StoreInfo, tree: Tree) {
    val errorPrefix = if (tree is VariableTree) "Object" else "Cannot override because object"

    // Even if there is a @Ensures in the enclosing method,
    // we should always check completion for example if there are assignments inside a loop,
    // which might create other references different from the one in the parameter.
    if (!TypecheckUtils.canDrop(value.jtcType)) {
      utils.err("$errorPrefix has not ended its protocol. Type: ${value.jtcType.format()}", tree)
    }

    val parameters = when (val method = TreeUtils.enclosingMethodOrLambda(currentPath)) {
      is MethodTree -> method.parameters
      is LambdaExpressionTree -> method.parameters
      else -> listOf()
    }
    val types = getParamTypesAfterCall(parameters)
    val finalType = types[name]

    if (finalType != null) {
      if (!value.jtcType.isSubtype(finalType)) {
        utils.err("$errorPrefix is not in the state specified by @Ensures. Type: ${value.jtcType.format()}", tree)
      }
    }
  }

  // Check that the array type of varargs is a subtype of the corresponding required varargs
  protected fun checkVarargs(element: ExecutableElement, tree: Tree) {
    if (!element.isVarArgs) {
      return
    }

    val parameters = element.parameters.map { it.asType() }
    val varargs = parameters.last() as Type.ArrayType

    val args = when (tree) {
      is MethodInvocationTree -> tree.arguments
      is NewClassTree -> tree.arguments
      else -> throw RuntimeException("unexpected tree")
    }

    // TODO
  }

  protected fun commonAssignmentCheck(left: Tree, right: Tree, errorKey: String) {
    commonAssignmentCheck(utils.factory.getAnnotatedType(left), left, utils.factory.getAnnotatedType(right), right, errorKey)

    when (left) {
      is VariableTree -> {
        // In case we are in a loop, ensure the object from the previous loop has completed its protocol
        val receiver = LocalVariable(TreeUtils.elementFromDeclaration(left))
        val leftValue = analyzer.getStoreBefore(left)[receiver] ?: return
        checkFinalType(receiver.toString(), leftValue, left)
      }
      is ExpressionTree -> {
        val receiver = getReference(left)
        val leftValue = receiver?.let { analyzer.getStoreBefore(left)[it] }
        checkFinalType(receiver?.toString() ?: "", leftValue ?: analyzer.getInitialInfo(left), left)

        if (left is JCTree.JCFieldAccess) {
          if (ElementUtils.isElementFromByteCode(left.selected.type.asElement())) {
            val type = analyzer.getInferredType(right)
            if (!type.isSubtype(TypecheckUtils.noProtocolTypes)) {
              utils.err("Assigning an object with protocol to a field that cannot be analyzed", left)
            }
          }
        }
      }
    }
  }

  protected fun commonAssignmentCheckParameter(varType: AnnotatedTypeMirror, valueExp: Tree, errorKey: String) {
    commonAssignmentCheck(varType, null, utils.factory.getAnnotatedType(valueExp), valueExp, errorKey, true)
  }

  protected fun commonAssignmentCheckReturn(varType: AnnotatedTypeMirror, valueExp: Tree) {
    commonAssignmentCheck(varType, null, utils.factory.getAnnotatedType(valueExp), valueExp, "return.type.incompatible", true)
  }

  private fun isPrimitiveAndBoxedPrimitive(aType: JTCType, bType: JTCType, bMirror: TypeMirror) =
    aType.isSubtype(JTCPrimitiveType.SINGLETON) && bType.isSubtype(JTCNoProtocolType.SINGLETON) && TypesUtils.isBoxedPrimitive(bMirror)

  protected fun commonAssignmentCheck(varType: AnnotatedTypeMirror, varTree: Tree?, valueType: AnnotatedTypeMirror, valueTree: Tree, errorKey: String, refine: Boolean = false) {
    if (varType is Type.ArrayType && valueTree is NewArrayTree && valueTree.type == null) {
      // TODO checkArrayInitialization(varType.componentType, valueTree.initializers)
    }

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
      if (!checkForNullability(valueTree as ExpressionTree, UNBOXING_OF_NULLABLE)) {
        // Only issue the unboxing of nullable error
        return
      }
    }

    val varInfo = if (varTree == null) analyzer.getInitialInfo(varType, refine) else analyzer.getInitialInfo(varTree)
    val varJTCType = varInfo.jtcType
    val valJTCType = analyzer.getInferredType(valueTree)

    // Assignments from boxed primitives to primitives and vice-versa should be allowed
    if (isPrimitiveAndBoxedPrimitive(varJTCType, valJTCType, valueType.underlyingType)) return
    if (isPrimitiveAndBoxedPrimitive(valJTCType, varJTCType, varType.underlyingType)) return

    if (!valJTCType.isSubtype(varJTCType)) {
      checker.reportError(
        valueTree,
        errorKey,
        "${valJTCType.format()} $valueType",
        "${varJTCType.format()} $varType"
      )
    }
  }

  protected fun printTypeInfo(path: TreePath, node: IdentifierTree) {
    if (checker.shouldReportTypeInfo() && !node.name.contentEquals("this")) {
      val parent = path.parentPath.leaf
      val type = if (parent is VariableTree || parent is AssignmentTree && parent.variable === node) {
        (analyzer.getStoreBefore(node)[getReference(node)!!] ?: analyzer.getInitialInfo(node)).jtcType
      } else {
        analyzer.getInferredType(node)
      }
      if (type !is JTCNoProtocolType && type !is JTCPrimitiveType) {
        checker.reportWarning(node, "$node: ${type.format()}")
      }
    }
  }

  protected fun isUnboxingOperation(tree: BinaryTree): Boolean {
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

  protected fun isString(tree: ExpressionTree): Boolean {
    val type = TreeUtils.typeOf(tree)
    return types.isAssignable(stringType, type)
  }

  protected fun isPrimitive(tree: ExpressionTree) = TreeUtils.typeOf(tree).kind.isPrimitive

  companion object {
    const val UNBOXING_OF_NULLABLE = "unboxing.of.nullable"
    const val LOCKING_NULLABLE = "locking.nullable"
    const val THROWING_NULLABLE = "throwing.nullable"
    const val ACCESSING_NULLABLE = "accessing.nullable"
    const val CONDITION_NULLABLE = "condition.nullable"
    const val ITERATING_NULLABLE = "iterating.over.nullable"
    const val SWITCHING_NULLABLE = "switching.nullable"
    const val DEREFERENCE_OF_NULLABLE = "dereference.of.nullable"
  }

}
