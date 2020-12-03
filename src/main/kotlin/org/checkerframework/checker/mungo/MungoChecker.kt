package org.checkerframework.checker.mungo

import com.sun.source.util.TreePath
import com.sun.tools.javac.processing.JavacProcessingEnvironment
import com.sun.tools.javac.util.Log
import org.checkerframework.checker.mungo.assertions.InferenceVisitor
import org.checkerframework.checker.mungo.typecheck.Typechecker
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.framework.source.SourceChecker
import org.checkerframework.framework.source.SourceVisitor
import java.io.IOException
import java.util.*
import javax.lang.model.element.TypeElement
import javax.tools.Diagnostic

const val showTypeInfoOpt = "showTypeInfo"
const val configFileOpt = "configFile"
const val inferenceOpt = "performInference"
const val messagesFile = "/messages.properties"

class MungoChecker : SourceChecker() {

  lateinit var utils: MungoUtils

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
    val utils = MungoUtils(this)
    utils.initFactory()
    this.utils = utils
  }

  // FIXME for some reason, there is an java.lang.InterruptedException exception when the code examples includes threads...
  private fun typeProcess2(e: TypeElement, p: TreePath) {
    val context = (processingEnv as JavacProcessingEnvironment).context
    val log = Log.instance(context)

    if (log.nerrors > errsOnLastExit) {
      println("${log.nerrors} > $errsOnLastExit")
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

  override fun typeProcess(e: TypeElement, p: TreePath) {
    println("TYPE PROCESS $e")
    typeProcess2(e, p)
    println("TYPE PROCESS END $e")
  }

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

}
