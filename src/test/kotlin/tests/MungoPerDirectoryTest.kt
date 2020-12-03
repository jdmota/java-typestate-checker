package tests

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest
import org.checkerframework.framework.test.TestConfigurationBuilder
import org.checkerframework.framework.test.TestUtilities
import org.junit.Test
import java.io.File
import java.util.*

val ignore = emptyList<String>()
val only = listOf("inference")

abstract class MungoPerDirectoryTest(val originalTestDir: String, testFiles: List<File>, opts: Array<String>) : CheckerFrameworkPerDirectoryTest(
  testFiles,
  MungoChecker::class.java,
  originalTestDir,
  *opts
) {
  @Test
  override fun run() {
    if (only.isNotEmpty() && !only.contains(originalTestDir)) {
      return
    }
    if (ignore.contains(originalTestDir)) {
      return
    }
    val shouldEmitDebugInfo = TestUtilities.getShouldEmitDebugInfo()
    val customizedOptions = customizeOptions(Collections.unmodifiableList(checkerOptions))
    val config = TestConfigurationBuilder.buildDefaultConfiguration(
      testDir,
      testFiles,
      setOf(checkerName),
      customizedOptions,
      shouldEmitDebugInfo)
    val testResult = MungoTypecheckExecutor(testDir).runTest(config)
    TestUtilities.assertResultsAreValid(testResult)
  }
}
