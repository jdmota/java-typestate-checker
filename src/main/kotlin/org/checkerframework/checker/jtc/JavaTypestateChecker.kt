package org.checkerframework.checker.jtc

import com.sun.source.tree.Tree
import com.sun.source.util.TreePath
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.util.Log
import org.checkerframework.checker.jtc.assertions.InferenceVisitor
import org.checkerframework.checker.jtc.typecheck.Typechecker
import org.checkerframework.checker.jtc.utils.JTCUtils
import org.checkerframework.framework.source.SourceChecker
import org.checkerframework.framework.source.SourceVisitor
import org.checkerframework.javacutil.BugInCF
import java.io.IOException
import java.util.*
import javax.lang.model.element.Element
import javax.lang.model.element.TypeElement
import javax.tools.Diagnostic

const val showTypeInfoOpt = "showTypeInfo"
const val configFileOpt = "configFile"
const val inferenceOpt = "performInference"
const val messagesFile = "/messages.properties"

class JavaTypestateChecker : SourceChecker() {

  lateinit var utils: JTCUtils

  override fun getSupportedOptions() = super.getSupportedOptions().plus(arrayOf(showTypeInfoOpt, inferenceOpt, configFileOpt))

  fun shouldReportTypeInfo() = hasOption(showTypeInfoOpt)

  private fun performInference() = hasOption(inferenceOpt)

  override fun createSourceVisitor(): SourceVisitor<*, *> {
    if (performInference()) {
      return InferenceVisitor(this)
    }
    return Typechecker(this)
  }

  override fun initChecker() {
    super.initChecker()
    val utils = JTCUtils(this)
    utils.initFactory()
    this.utils = utils
  }

  // FIXME for some reason, there is an java.lang.InterruptedException exception when the code examples includes threads...
  private fun typeProcess2(e: TypeElement, p: TreePath) {
    val context = (processingEnv as JavacProcessingEnvironment).context
    val log = Log.instance(context)

    if (log.nerrors > errsOnLastExit) {
      // println("${log.nerrors} > $errsOnLastExit")
      errsOnLastExit = log.nerrors
      // return
    }

    if (visitor == null) {
      return
    }

    if (p.compilationUnit !== currentRoot) {
      setRoot(p.compilationUnit)
    }

    try {
      visitor.visit(p)
      warnUnneededSuppressions()
    } catch (e: Throwable) {
      e.printStackTrace()
      throw e
    }
  }

  /*override fun typeProcess(e: TypeElement, p: TreePath) {
    println("TYPE PROCESS $e")
    typeProcess2(e, p)
    println("TYPE PROCESS END $e")
  }*/

  override fun typeProcessingOver() {
    val visitor = this.visitor
    if (visitor is InferenceVisitor) {
      visitor.inferrer.phase2()
    }
  }

  private fun getProperties(): Properties {
    val prop = Properties()
    try {
      val stream = javaClass.getResourceAsStream(messagesFile)
      prop.load(stream)
    } catch (e: IOException) {
      message(Diagnostic.Kind.WARNING, "Couldn't parse properties file: $messagesFile")
    }
    return prop
  }

  override fun getMessagesProperties(): Properties {
    return if (messagesProperties != null) {
      messagesProperties
    } else {
      messagesProperties = Properties()
      messagesProperties.putAll(getProperties())
      messagesProperties
    }
  }

  private fun shouldFixErrorMsg(): Boolean {
    val opts = processingEnv.options ?: return true
    return !opts.containsKey("nomsgtext") && !opts.containsKey("detailedmsgtext")
  }

  override fun reportError(source: Any, messageKey: String, vararg args: Any?) {
    if (shouldFixErrorMsg()) {
      report(source, Diagnostic.Kind.ERROR, messageKey, *args)
    } else {
      super.reportError(source, messageKey, *args)
    }
  }

  override fun reportWarning(source: Any, messageKey: String, vararg args: Any?) {
    if (shouldFixErrorMsg()) {
      report(source, Diagnostic.Kind.MANDATORY_WARNING, messageKey, *args)
    } else {
      super.reportWarning(source, messageKey, *args)
    }
  }

  // Adapted from SourceChecker
  private fun report(source: Any, _kind: Diagnostic.Kind, messageKey: String, vararg _args: Any?) {
    if (shouldSuppressWarnings(source, messageKey)) {
      return
    }

    var kind = _kind
    val args = _args.map { processArg(it) }.toTypedArray()

    val defaultFormat = "($messageKey)"
    val part1 = suppressWarningsString(messageKey)
    val part2 = fullMessageOf(messageKey, defaultFormat)
    val fmtString = if ("($part1)" == part2) part1 else "[$part1] $part2"

    val messageText = try {
      String.format(fmtString, *args)
    } catch (e: Exception) {
      throw BugInCF("Invalid format string: \"$fmtString", e)
    }

    if (kind == Diagnostic.Kind.ERROR && hasOption("warns")) {
      kind = Diagnostic.Kind.MANDATORY_WARNING
    }

    when (source) {
      is Element -> messager.printMessage(kind, messageText, source)
      is Tree -> printOrStoreMessage(kind, messageText, source, currentRoot)
      else -> throw BugInCF("invalid position source, class=" + source.javaClass)
    }
  }

  // From SourceChecker
  private fun shouldSuppressWarnings(src: Any?, errKey: String): Boolean {
    return when (src) {
      is Element -> shouldSuppressWarnings(src, errKey)
      is Tree -> shouldSuppressWarnings(src, errKey)
      null -> false
      else -> throw BugInCF("Unexpected source $src")
    }
  }

  // From SourceChecker
  private fun suppressWarningsString(messageKey: String): String {
    val prefixes: MutableCollection<String> = this.suppressWarningsPrefixes
    prefixes.remove(SUPPRESS_ALL_PREFIX)
    return if (hasOption("showSuppressWarningsStrings")) {
      val list: MutableList<String> = ArrayList(prefixes)
      // Make sure "allcheckers" is at the end of the list.
      if (useAllcheckersPrefix) {
        list.add(SUPPRESS_ALL_PREFIX)
      }
      "$list:$messageKey"
    } else if (hasOption("requirePrefixInWarningSuppressions")) {
      // If the warning key must be prefixed with a prefix (a checker name), then add that to
      // the SuppressWarnings string that is printed.
      val defaultPrefix = getDefaultSuppressWarningsPrefix()
      if (prefixes.contains(defaultPrefix)) {
        "$defaultPrefix:$messageKey"
      } else {
        val firstKey = prefixes.iterator().next()
        "$firstKey:$messageKey"
      }
    } else {
      messageKey
    }
  }

  // From SourceChecker
  private fun getDefaultSuppressWarningsPrefix(): String {
    val className = this.javaClass.simpleName
    var indexOfChecker = className.lastIndexOf("Checker")
    if (indexOfChecker == -1) {
      indexOfChecker = className.lastIndexOf("Subchecker")
    }
    val result = if (indexOfChecker == -1) className else className.substring(0, indexOfChecker)
    return result.toLowerCase()
  }

}
