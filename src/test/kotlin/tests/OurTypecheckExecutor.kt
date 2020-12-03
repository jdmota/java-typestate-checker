package tests

import org.checkerframework.framework.test.CompilationResult
import org.checkerframework.framework.test.TestConfiguration
import org.checkerframework.framework.test.TypecheckExecutor
import org.checkerframework.framework.test.TypecheckResult
import org.checkerframework.framework.test.diagnostics.JavaDiagnosticReader
import org.checkerframework.framework.test.diagnostics.TestDiagnostic
import java.io.File
import java.util.*
import java.util.regex.Pattern
import javax.tools.Diagnostic
import javax.tools.JavaFileObject

class OurTypecheckExecutor(private val testDir: String) : TypecheckExecutor() {
  private class OurDiagnostic<F : JavaFileObject>(private val d: Diagnostic<F>) : Diagnostic<F> {
    override fun getKind(): Diagnostic.Kind = d.kind
    override fun getSource(): F = d.source
    override fun getPosition() = d.position
    override fun getStartPosition() = d.startPosition
    override fun getEndPosition() = d.endPosition
    override fun getLineNumber() = d.lineNumber
    override fun getColumnNumber() = d.columnNumber
    override fun getCode(): String = fix(d.code)
    override fun getMessage(locale: Locale?): String = fix(d.getMessage(locale))
    override fun toString(): String = fix(d.toString()).replace(".protocol:", ".protocol.java:") // Hack
  }

  override fun interpretResults(config: TestConfiguration, compilationResult: CompilationResult): TypecheckResult {
    fixResult(compilationResult)
    val expectedDiagnostics = readDiagnostics(config, compilationResult)
    val allExpected = extendExpected(expectedDiagnostics)
    return TypecheckResult.fromCompilationResults(config, compilationResult, allExpected)
  }

  // Support expecting errors from protocol files
  private fun extendExpected(expected: List<TestDiagnostic>): List<TestDiagnostic> {
    val dir = File(testDir)
    val list = dir.list() ?: emptyArray<String>()
    val protocols = list.filter { it.endsWith(".protocol") }.map { File(dir, it) }
    val expectedFromProtocols = JavaDiagnosticReader.readJavaSourceFiles(protocols).map {
      val file = it.filename.replace(".protocol", ".protocol.java") // Hack
      TestDiagnostic(file, it.lineNumber, it.kind, it.message, it.isFixable, it.shouldOmitParentheses())
    }
    return expected.plus(expectedFromProtocols)
  }

  companion object {
    private const val CRLF = "\r\n"
    private val pattern = Pattern.compile("\r?\n")
    private val isWin = System.lineSeparator() == CRLF
    private fun fix(str: String) = pattern.matcher(str).replaceAll(CRLF)
    private fun fixResult(result: CompilationResult) {
      // Workaround issue introduced in https://github.com/typetools/checker-framework/pull/3091
      // where -Anomsgtext stopped working properly in Windows where source files use LF instead of CRLF
      if (isWin) {
        try {
          val clazz = result.javaClass
          val field = clazz.getDeclaredField("diagnostics")
          field.isAccessible = true
          field[result] = result.diagnostics.map { OurDiagnostic(it) }
        } catch (e: Exception) {
          e.printStackTrace()
        }
      }
    }
  }
}
