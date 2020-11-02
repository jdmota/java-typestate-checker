package org.checkerframework.checker.mungo.assertions

import com.sun.source.util.TreePathScanner
import com.sun.tools.javac.code.Symbol
import com.sun.tools.javac.tree.JCTree
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.analysis.*
import org.checkerframework.dataflow.cfg.UnderlyingAST
import org.checkerframework.org.plumelib.util.WeakIdentityHashMap
import javax.lang.model.element.ElementKind

// TODO fix infinite recursion with recursive data types like Node.next.next.next
class LocationsGatherer(private val checker: MungoChecker) : TreePathScanner<Void?, Void?>() {

  val utils get() = checker.utils

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
    }
    return list
  }

  private val cache1 = WeakIdentityHashMap<JCTree, List<Reference>>()
  private val cache2 = WeakIdentityHashMap<Symbol.MethodSymbol, List<Reference>>()

  fun getParameterLocations(method: JCTree.JCLambda): List<Reference> {
    return cache1.computeIfAbsent(method) {
      method.parameters.fold(mutableListOf()) { l, param ->
        val ref = createParameterVariable(param)
        getLocationsHelper(l, ref)
        getLocationsHelper(l, ref.toLocalVariable())
      }
    }
  }

  fun getParameterLocations(method: JCTree.JCMethodDecl): List<Reference> {
    val sym = method.sym
    return cache1.computeIfAbsent(method) {
      val list = mutableListOf<Reference>()
      if (!sym.isStatic) {
        getLocationsHelper(list, ThisReference(sym.enclosingElement.asType()))
      }
      sym.parameters.fold(list) { l, param ->
        val ref = ParameterVariable(param)
        getLocationsHelper(l, ref)
        getLocationsHelper(l, ref.toLocalVariable())
      }
    }
  }

  fun getParameterLocationsForCall(sym: Symbol.MethodSymbol): List<Reference> {
    return cache2.computeIfAbsent(sym) {
      val isConstructor = sym.getKind() == ElementKind.CONSTRUCTOR
      val list = mutableListOf<Reference>()
      if (!sym.isStatic && !isConstructor) {
        list.add(ThisReference(sym.enclosingElement.asType()))
      }
      sym.parameters.fold(list) { l, param ->
        l.add(ParameterVariable(param))
        l
      }
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
