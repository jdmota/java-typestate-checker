package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.ClassTree
import com.sun.source.tree.Tree
import com.sun.source.tree.VariableTree
import com.sun.source.util.TreePathScanner
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.analysis.prepareClass
import org.checkerframework.checker.mungo.utils.treeToElement
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import javax.lang.model.element.Element
import javax.lang.model.type.TypeMirror

// TODO fix infinite recursion with recursive data types like Node.next.next.next
class LocationsGatherer(private val inferrer: Inferrer) : TreePathScanner<Void?, Void?>() {

  private fun getFields(classTree: ClassTree): List<VariableTree> {
    return prepareClass(classTree).nonStatic.fields
  }

  private fun getFields(element: Element): List<VariableTree> {
    val tree = inferrer.utils.treeUtils.getTree(element)
    if (tree is ClassTree) return getFields(tree)
    return emptyList()
  }

  private fun getLocations(name: String, element: Element): MutableList<Pair<String, TypeMirror>> {
    val list = mutableListOf(Pair(name, element.asType()))
    getFields(element).forEach { list.addAll(getLocations(name, it)) }
    return list
  }

  private fun getLocations(prefix: String, tree: VariableTree): MutableList<Pair<String, TypeMirror>> {
    val name = if (prefix.isEmpty()) tree.name.toString() else "$prefix.${tree.name}"
    val element = treeToElement(tree)
    return getLocations(name, element)
  }

  private fun getLocations(method: JCTree.JCLambda): List<Pair<String, TypeMirror>> {
    return cache.computeIfAbsent(method) {
      val list = mutableListOf<Pair<String, TypeMirror>>()
      method.parameters.forEach { list.addAll(getLocations("", it)) }
      list
    }
  }

  private val cache = WeakIdentityHashMap<Tree, List<Pair<String, TypeMirror>>>()

  private fun getLocations(method: JCTree.JCMethodDecl): List<Pair<String, TypeMirror>> {
    return cache.computeIfAbsent(method) {
      val sym = method.sym
      val list = if (sym.isConstructor || sym.isStatic) {
        mutableListOf()
      } else {
        getLocations("this", sym.enclosingElement)
      }
      method.parameters.forEach { list.addAll(getLocations("", it)) }
      list
    }
  }

  fun getLocations(sym: Symbol.MethodSymbol): List<Pair<String, TypeMirror>>? {
    val tree = inferrer.utils.treeUtils.getTree(sym) ?: return null
    return getLocations(tree as JCTree.JCMethodDecl)
  }

  fun getLocations(ast: UnderlyingAST): List<Pair<String, TypeMirror>>? {
    return when (ast) {
      is UnderlyingAST.CFGMethod -> getLocations(ast.method as JCTree.JCMethodDecl)
      is UnderlyingAST.CFGLambda -> getLocations(ast.lambdaTree as JCTree.JCLambda)
      else -> null
    }
  }

}
