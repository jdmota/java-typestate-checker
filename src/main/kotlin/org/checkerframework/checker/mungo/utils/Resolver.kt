package org.checkerframework.checker.mungo.utils

import com.sun.source.tree.Scope
import com.sun.source.util.TreePath
import com.sun.source.util.Trees
import com.sun.tools.javac.api.JavacScope
import com.sun.tools.javac.code.*
import com.sun.tools.javac.code.Symbol.*
import com.sun.tools.javac.comp.*
import com.sun.tools.javac.file.JavacFileManager
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.tree.JCTree
import com.sun.tools.javac.tree.TreeMaker
import com.sun.tools.javac.util.List
import com.sun.tools.javac.util.Name
import com.sun.tools.javac.util.Names
import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.checker.mungo.typestate.TIdNode
import org.checkerframework.checker.mungo.typestate.TMemberNode
import org.checkerframework.checker.mungo.typestate.TRefNode
import org.checkerframework.checker.mungo.typestate.TTypestateNode
import org.checkerframework.checker.mungo.typestate.graph.Graph
import java.lang.reflect.Method
import java.nio.file.Path
import javax.lang.model.element.Element
import javax.tools.JavaFileManager

// Adapted from org.checkerframework.javacutil.Resolver
class Resolver(checker: MungoChecker) {

  private val ctx = (checker.processingEnvironment as JavacProcessingEnvironment).context
  private val trees = Trees.instance(checker.processingEnvironment)
  private val symtab = Symtab.instance(ctx)
  private val names = Names.instance(ctx)
  private val resolve = Resolve.instance(ctx)
  private val maker = TreeMaker.instance(ctx)
  private val enter = Enter.instance(ctx)
  private val modules = Modules.instance(ctx)
  private val fileManager = ctx.get(JavaFileManager::class.java) as JavacFileManager

  private val findType = Resolve::class.java.getDeclaredMethod("findType", Env::class.java, Name::class.java)
  private val findIdent = Resolve::class.java.getDeclaredMethod("findIdent", Env::class.java, Name::class.java, Kinds.KindSelector::class.java)
  private val findIdentInPackage = Resolve::class.java.getDeclaredMethod("findIdentInPackage", Env::class.java, TypeSymbol::class.java, Name::class.java, Kinds.KindSelector::class.java)

  init {
    findType.isAccessible = true
    findIdent.isAccessible = true
    findIdentInPackage.isAccessible = true
  }

  private fun refToJCExpression(ref: TRefNode): JCTree.JCExpression {
    return when (ref) {
      is TIdNode -> maker.Ident(names.fromString(ref.name))
      is TMemberNode -> maker.Select(refToJCExpression(ref.ref), names.fromString(ref.id.name))
    }
  }

  fun createEnv(userPath: Path, typestate: TTypestateNode): Env<AttrContext>? {

    val pkg = typestate.pkg?.let {
      maker.PackageDecl(List.nil(), refToJCExpression(it.ref))
    }

    val imports: List<JCTree> = List.from(typestate.imports.map {
      val expr = if (it.star) maker.Select(refToJCExpression(it.ref), names.asterisk) else refToJCExpression(it.ref)
      maker.Import(expr, it.static)
    })

    val tree = maker.TopLevel(if (pkg == null) imports else imports.prepend(pkg))
    tree.sourcefile = fileManager.getJavaFileObject(userPath)

    return if (modules.enter(List.of(tree), null)) {
      enter.complete(List.of(tree), null)
      getEnvForPath(TreePath(tree))
    } else {
      null
    }
  }

  private fun getEnvForPath(path: TreePath): Env<AttrContext>? {
    var iter: TreePath? = path
    var scope: Scope? = null
    while (scope == null && iter != null) {
      try {
        scope = trees.getScope(iter)
      } catch (t: Throwable) {
        iter = iter.parentPath
      }
    }
    return (scope as? JavacScope)?.env
  }

  private fun findClass(name: String, env: Env<AttrContext>): Element? {
    return wrapInvocationOnResolveInstance(findType, env, names.fromString(name))
  }

  private fun findPackage(name: String, env: Env<AttrContext>): PackageSymbol? {
    val res = wrapInvocationOnResolveInstance(
      findIdent,
      env,
      names.fromString(name),
      Kinds.KindSelector.PCK)
    val ps = res as? PackageSymbol ?: return null
    return if (ps.exists()) ps else null
  }

  private fun findClassInPackage(name: String, pck: PackageSymbol, env: Env<AttrContext>): ClassSymbol? {
    val res = wrapInvocationOnResolveInstance(
      findIdentInPackage,
      env,
      pck,
      names.fromString(name),
      Kinds.KindSelector.TYP)
    return res as? ClassSymbol
  }

  fun resolve(env: Env<AttrContext>, name: String): Type? {
    return when (name) {
      "byte" -> symtab.byteType
      "char" -> symtab.charType
      "short" -> symtab.shortType
      "int" -> symtab.intType
      "long" -> symtab.longType
      "float" -> symtab.floatType
      "double" -> symtab.doubleType
      "boolean" -> symtab.booleanType
      "void" -> symtab.voidType
      else -> {
        val parts = name.split(".")
        if (parts.size == 1) {
          (findClass(parts[0], env) as? Symbol)?.type
        } else {
          // So that things like java.lang.Object can be resolved
          val pkgName = parts.subList(0, parts.size - 1).joinToString(".")
          val pkg = findPackage(pkgName, env) ?: return null
          val className = parts[parts.lastIndex]
          findClassInPackage(className, pkg, env)?.asType()
        }
      }
    }
  }

  private fun wrapInvocationOnResolveInstance(method: Method, vararg args: Any): Symbol? {
    return try {
      wrapInvocation(resolve, method, *args)
    } catch (t: Throwable) {
      null
    }
  }

  private fun wrapInvocation(receiver: Any, method: Method, vararg args: Any): Symbol? {
    return try {
      method.invoke(receiver, *args) as? Symbol
    } catch (t: Throwable) {
      null
    }
  }

}
