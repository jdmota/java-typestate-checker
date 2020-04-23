package tests

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest
import org.checkerframework.framework.test.TestConfigurationBuilder
import org.checkerframework.framework.test.TestUtilities
import org.junit.Test
import org.junit.runners.Parameterized.Parameters
import java.io.File
import java.util.*

/**
 * Test runner for tests of the Mungo Checker.
 *
 * Tests appear as Java files in the `tests/mungo` folder. To add a new test case,
 * create a Java file in that directory. The file contains "// ::" comments to indicate expected
 * errors and warnings; see
 * https://github.com/typetools/checker-framework/blob/master/checker/tests/README
 */
class MungoTest(testFiles: List<File>) : CheckerFrameworkPerDirectoryTest(
  testFiles,
  MungoChecker::class.java,
  "mungo",
  "-Anomsgtext", "-AshowTypeInfo"
) {
  @Test
  override fun run() {
    val shouldEmitDebugInfo = TestUtilities.getShouldEmitDebugInfo()
    val customizedOptions = customizeOptions(Collections.unmodifiableList(checkerOptions))
    val config = TestConfigurationBuilder.buildDefaultConfiguration(
      testDir,
      testFiles, setOf(checkerName),
      customizedOptions,
      shouldEmitDebugInfo)
    val testResult = MungoTypecheckExecutor(testDir).runTest(config)
    TestUtilities.assertResultsAreValid(testResult)
  }

  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs
      get() = arrayOf("mungo")
  }
}
