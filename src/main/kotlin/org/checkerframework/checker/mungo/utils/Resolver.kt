package org.checkerframework.checker.mungo.utils

import com.sun.tools.javac.code.*
import com.sun.tools.javac.code.Symbol.CompletionFailure
import com.sun.tools.javac.comp.AttrContext
import com.sun.tools.javac.comp.Enter
import com.sun.tools.javac.comp.Env
import com.sun.tools.javac.comp.Resolve
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.util.Convert
import com.sun.tools.javac.util.Name
import com.sun.tools.javac.util.Names
import javax.lang.model.element.ElementVisitor

// Adapted from com.sun.tools.javac.comp.Resolve

class Resolver(env: JavacProcessingEnvironment) {

  private val names = Names.instance(env.context)
  private val resolve = Resolve.instance(env.context)
  private val finder = ClassFinder.instance(env.context)
  private val enter = Enter.instance(env.context)
  private val typeNotFound = SymbolNotFoundError(Kinds.Kind.ABSENT_TYP)

  private fun loadClass(env: Env<AttrContext>, name: Name, recoveryLoadClass: (Env<AttrContext>, Name) -> Symbol?): Symbol {
    return try {
      val c = finder.loadClass(env.toplevel.modle, name)
      if (resolve.isAccessible(env, c)) c else AccessError(c)
    } catch (err: ClassFinder.BadClassFile) {
      throw err
    } catch (ex: CompletionFailure) {
      val candidate = recoveryLoadClass(env, name)
      candidate ?: typeNotFound
    }
  }

  private fun bestOf(s1: Symbol, s2: Symbol): Symbol {
    return if (s1.kind.betterThan(s2.kind)) s1 else s2
  }

  private fun findGlobalType(env: Env<AttrContext>, scope: Scope, name: Name, recoveryLoadClass: (Env<AttrContext>, Name) -> Symbol?): Symbol {
    var bestSoFar: Symbol = typeNotFound
    for (s in scope.getSymbolsByName(name)) {
      val sym = loadClass(env, s.flatName(), recoveryLoadClass)
      bestSoFar =
        if (bestSoFar.kind == Kinds.Kind.TYP && sym.kind == Kinds.Kind.TYP && bestSoFar !== sym)
          return AmbiguityError(bestSoFar, sym)
        else bestOf(bestSoFar, sym)
    }
    return bestSoFar
  }

  fun resolve(toplevel: JCTree.JCCompilationUnit, name: Name): Symbol {
    val env = enter.getTopLevelEnv(toplevel);
    var bestSoFar: Symbol = typeNotFound

    var sym: Symbol = findGlobalType(env, toplevel.namedImportScope, name, namedImportScopeRecovery)
    bestSoFar = if (sym.exists()) return sym else bestOf(bestSoFar, sym)

    sym = findGlobalType(env, toplevel.packge.members(), name, noRecovery)
    bestSoFar = if (sym.exists()) return sym else bestOf(bestSoFar, sym)

    sym = findGlobalType(env, toplevel.starImportScope, name, starImportScopeRecovery)
    bestSoFar = if (sym.exists()) return sym else bestOf(bestSoFar, sym)

    return bestSoFar
  }

  fun resolve(toplevel: JCTree.JCCompilationUnit, string: String): Symbol {
    return resolve(toplevel, names.fromString(string))
  }

  abstract class ResolveError(kind: Kinds.Kind, private val debugName: String) : Symbol(kind, 0, null, null, null) {
    override fun <R, P> accept(v: ElementVisitor<R, P>, p: P): R {
      throw AssertionError()
    }

    override fun toString(): String {
      return debugName
    }

    override fun exists(): Boolean {
      return false
    }

    override fun isStatic(): Boolean {
      return false
    }
  }

  abstract class InvalidSymbolError(kind: Kinds.Kind, val sym: Symbol, debugName: String) : ResolveError(kind, debugName) {
    override fun exists(): Boolean {
      return true
    }
  }

  class AccessError(sym: Symbol) : InvalidSymbolError(Kinds.Kind.HIDDEN, sym, "access error") {
    override fun exists(): Boolean {
      return false
    }
  }

  class SymbolNotFoundError(kind: Kinds.Kind, debugName: String = "symbol not found error") : ResolveError(kind, debugName)

  class AmbiguityError(val sym1: Symbol, val sym2: Symbol) : ResolveError(Kinds.Kind.AMBIGUOUS, "ambiguity error") {
    override fun exists(): Boolean {
      return true
    }
  }

  class InvisibleSymbolError(sym: Symbol) : InvalidSymbolError(Kinds.Kind.HIDDEN, sym, "invisible class error")

  private val noRecovery = { _: Env<AttrContext>, _: Name? -> null }

  private val namedImportScopeRecovery = { env: Env<AttrContext>, name: Name ->
    val importScope: Scope = env.toplevel.namedImportScope
    val existing = importScope.findFirst(Convert.shortName(name)) { sym: Symbol -> sym.kind == Kinds.Kind.TYP && sym.flatName() === name }
    if (existing != null) InvisibleSymbolError(existing) else null
  }

  private val starImportScopeRecovery = { env: Env<AttrContext>, name: Name ->
    val importScope: Scope = env.toplevel.starImportScope
    var existing = importScope.findFirst(Convert.shortName(name)) { sym: Symbol -> sym.kind == Kinds.Kind.TYP && sym.flatName() === name }
    if (existing != null) {
      try {
        existing = finder.loadClass(existing.packge().modle, name)
        InvisibleSymbolError(existing)
      } catch (cf: CompletionFailure) {
        null
      }
    } else null
  }

}
