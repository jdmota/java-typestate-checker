package org.checkerframework.checker.mungo

import com.sun.tools.javac.util.JCDiagnostic
import org.checkerframework.checker.mungo.typecheck.MungoVisitor
import org.checkerframework.checker.mungo.utils.MungoUtils
import org.checkerframework.common.basetype.BaseTypeChecker
import org.checkerframework.common.basetype.BaseTypeVisitor
import org.checkerframework.javacutil.BugInCF
import java.nio.file.Path
import java.util.*

const val showTypeInfoOpt = "showTypeInfo"
const val configFile = "configFile"

/**
 * This is the entry point for pluggable type-checking.
 */
class MungoChecker : BaseTypeChecker() {

  private val _utils = MungoUtils.LazyField { MungoUtils(this) }
  val utils get() = _utils.get()

  override fun createSourceVisitor(): BaseTypeVisitor<*> {
    return MungoVisitor(this)
  }

  override fun getSupportedOptions() = super.getSupportedOptions().plus(showTypeInfoOpt).plus(configFile)

  fun shouldReportTypeInfo() = hasOption(showTypeInfoOpt)

  fun getConfigFile(): String? = getOption(configFile, null)

  // Adapted from SourceChecker#report and JavacTrees#printMessage
  fun reportError(file: Path, pos: Int, messageKey: String, vararg args: Any?) {
    val defaultFormat = "($messageKey)"
    val fmtString = if (processingEnv.options != null && processingEnv.options.containsKey("nomsgtext")) {
      defaultFormat
    } else if (processingEnv.options != null && processingEnv.options.containsKey("detailedmsgtext")) {
      // TODO detailedMsgTextPrefix(source, defaultFormat, args) + fullMessageOf(messageKey, defaultFormat)
      defaultFormat
    } else {
      // TODO "[" + suppressionKey(messageKey) + "] " + fullMessageOf(messageKey, defaultFormat)
      defaultFormat
    }
    val messageText = try {
      String.format(fmtString, *args)
    } catch (e: Exception) {
      throw BugInCF("Invalid format string: \"$fmtString\" args: " + args.contentToString(), e)
    }

    val newSource = utils.fileManager.getJavaFileObject(MungoUtils.getUserPath(file))
    val oldSource = utils.log.useSource(newSource)
    try {
      utils.log.error(JCDiagnostic.DiagnosticFlag.MULTIPLE, JCDiagnostic.SimpleDiagnosticPosition(pos), "proc.messager", messageText)
    } finally {
      utils.log.useSource(oldSource)
    }
  }
}
