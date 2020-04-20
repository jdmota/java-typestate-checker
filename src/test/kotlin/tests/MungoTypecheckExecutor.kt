package tests

import org.checkerframework.framework.test.TestConfiguration
import org.checkerframework.framework.test.TypecheckExecutor
import org.checkerframework.framework.test.TypecheckResult
import java.util.*
import java.util.regex.Pattern
import javax.tools.Diagnostic
import javax.tools.JavaFileObject

class MungoTypecheckExecutor : TypecheckExecutor() {
  private class MungoDiagnostic<F : JavaFileObject>(private val d: Diagnostic<F>) : Diagnostic<F> {
    override fun getKind(): Diagnostic.Kind = d.kind
    override fun getSource(): F = d.source
    override fun getPosition() = d.position
    override fun getStartPosition() = d.startPosition
    override fun getEndPosition() = d.endPosition
    override fun getLineNumber() = d.lineNumber
    override fun getColumnNumber() = d.columnNumber
    override fun getCode() = fix(d.code)
    override fun getMessage(locale: Locale) = fix(d.getMessage(locale))
    override fun toString() = fix(d.toString())
  }

  override fun runTest(configuration: TestConfiguration): TypecheckResult {
    val result = compile(configuration)
    // Workaround issue introduced in https://github.com/typetools/checker-framework/pull/3091
    // where -Anomsgtext stopped working properly in Windows where source files use LF instead of CRLF
    if (isWin) {
      try {
        val clazz = result.javaClass
        val field = clazz.getDeclaredField("diagnostics")
        field.isAccessible = true
        field[result] = result.diagnostics.map { MungoDiagnostic(it) }
      } catch (e: Exception) {
        e.printStackTrace()
      }
    }
    return interpretResults(configuration, result)
  }

  companion object {
    private const val CRLF = "\r\n"
    private val pattern = Pattern.compile("\r?\n")
    private val isWin = System.lineSeparator() == CRLF
    private fun fix(str: String) = pattern.matcher(str).replaceAll(CRLF)
  }
}
