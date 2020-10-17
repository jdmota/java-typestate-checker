package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.ClassTree
import com.sun.source.tree.Tree
import com.sun.source.tree.VariableTree
import com.sun.source.util.TreePathScanner
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.checker.mungo.utils.treeToElement
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import javax.lang.model.element.Element

// TODO fix infinite recursion with recursive data types like Node.next.next.next
class LocationsGatherer(private val checker: MungoChecker) : TreePathScanner<Void?, Void?>() {

  private fun getFields(classTree: ClassTree): List<VariableTree> {
    return prepareClass(classTree).nonStatic.fields
  }

  private fun getFields(element: Element): List<VariableTree> {
    val tree = checker.utils.treeUtils.getTree(element)
    if (tree is ClassTree) return getFields(tree)
    return emptyList()
  }

  fun getLocations(ref: Reference): MutableList<Reference> {
    val element = checker.utils.typeUtils.asElement(ref.type)
    val list = mutableListOf(ref)
    if (element != null) {
      getFields(element).forEach { list.addAll(getLocations(ref, it)) }
    }
    return list
  }

  private fun getLocations(prefix: Reference?, tree: VariableTree): MutableList<Reference> {
    return getLocations(if (prefix == null) createLocalVariable(tree) else createFieldAccess(prefix, tree))
  }

  private fun getParameterLocations(method: JCTree.JCLambda): List<Reference> {
    return cache.computeIfAbsent(method) {
      val list = mutableListOf<Reference>()
      method.parameters.forEach { list.addAll(getLocations(null, it)) }
      list
    }
  }

  private val cache = WeakIdentityHashMap<Tree, List<Reference>>()

  private fun getParameterLocations(method: JCTree.JCMethodDecl): List<Reference> {
    return cache.computeIfAbsent(method) {
      val sym = method.sym
      val list = if (sym.isStatic) {
        mutableListOf()
      } else {
        getLocations(ThisReference(sym.enclosingElement.asType()))
      }
      method.parameters.forEach { list.addAll(getLocations(null, it)) }
      list
    }
  }

  fun getParameterLocations(sym: Symbol.MethodSymbol): List<Reference> {
    val tree = checker.utils.treeUtils.getTree(sym) ?: return emptyList()
    return getParameterLocations(tree as JCTree.JCMethodDecl)
  }

  fun getParameterLocations(ast: UnderlyingAST): List<Reference> {
    return when (ast) {
      is UnderlyingAST.CFGMethod -> getParameterLocations(ast.method as JCTree.JCMethodDecl)
      is UnderlyingAST.CFGLambda -> getParameterLocations(ast.lambdaTree as JCTree.JCLambda)
      else -> emptyList()
    }
  }

}
