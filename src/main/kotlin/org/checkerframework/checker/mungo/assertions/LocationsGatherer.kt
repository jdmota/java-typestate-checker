package org.checkerframework.checker.mungo.assertions

import com.sun.source.tree.Tree
import com.sun.source.util.TreePathScanner
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap

// TODO fix infinite recursion with recursive data types like Node.next.next.next
class LocationsGatherer(private val checker: MungoChecker) : TreePathScanner<Void?, Void?>() {

  val utils get() = checker.utils

  /*private fun getFields(classTree: ClassTree): List<VariableTree> {
    return prepareClass(classTree).nonStatic.fields
  }

  private fun getFields(element: Element): List<VariableTree> {
    val tree = checker.utils.treeUtils.getTree(element)
    if (tree is ClassTree) return getFields(tree)
    return emptyList()
  }*/

  fun getLocations(ref: Reference): List<Reference> {
    val list = mutableListOf<Reference>()
    getLocationsHelper(list, ref)
    return list
  }

  private fun getLocationsHelper(list: MutableList<Reference>, ref: Reference): MutableList<Reference> {
    list.add(ref)

    val element = utils.typeUtils.asElement(ref.type)
    if (element is Symbol.ClassSymbol) {
      val pkg = utils.elementUtils.getPackageOf(element).qualifiedName.toString()
      // Avoid recursion...
      if (!pkg.startsWith("java.")) {
        element.members_field?.symbols?.filterIsInstance(Symbol.VarSymbol::class.java)?.forEach {
          getLocationsHelper(list, FieldAccess(ref, it))
        }
      }
      // getFields(element).forEach { list.addAll(getLocations(ref, it)) }
    }
    return list
  }

  private val cache1 = WeakIdentityHashMap<Tree, List<Reference>>()
  private val cache2 = WeakIdentityHashMap<Symbol, List<Reference>>()

  private fun getParameterLocations(method: JCTree.JCLambda): List<Reference> {
    return cache1.computeIfAbsent(method) {
      method.parameters.fold(mutableListOf()) { l, param -> getLocationsHelper(l, createLocalVariable(param)) }
    }
  }

  fun getParameterLocations(method: JCTree.JCMethodDecl): List<Reference> {
    return cache1.computeIfAbsent(method) {
      val sym = method.sym
      val list = mutableListOf<Reference>()
      if (!sym.isStatic) {
        getLocationsHelper(list, ThisReference(sym.enclosingElement.asType()))
      }
      method.parameters.fold(list) { l, param -> getLocationsHelper(l, createLocalVariable(param)) }
    }
  }

  fun getParameterLocations(sym: Symbol.MethodSymbol): List<Reference> {
    /*val tree = checker.utils.treeUtils.getTree(sym)
    return getParameterLocations(tree as JCTree.JCMethodDecl)*/
    return cache2.computeIfAbsent(sym) {
      val list = mutableListOf<Reference>()
      if (!sym.isStatic) {
        getLocationsHelper(list, ThisReference(sym.enclosingElement.asType()))
      }
      sym.parameters.fold(list) { l, param -> getLocationsHelper(l, LocalVariable(param)) }
    }
  }

  fun getParameterLocations(ast: UnderlyingAST): List<Reference> {
    return when (ast) {
      is UnderlyingAST.CFGMethod -> getParameterLocations(ast.method as JCTree.JCMethodDecl)
      is UnderlyingAST.CFGLambda -> getParameterLocations(ast.lambdaTree as JCTree.JCLambda)
      else -> emptyList()
    }
  }

}
