package tests

import org.checkerframework.checker.mungo.MungoChecker
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest
import org.checkerframework.framework.test.TestConfigurationBuilder
import org.checkerframework.framework.test.TestUtilities
import org.junit.Test
import java.io.File
import java.util.*

abstract class MungoPerDirectoryTest(testDir: String, testFiles: List<File>) : CheckerFrameworkPerDirectoryTest(
  testFiles,
  MungoChecker::class.java,
  testDir,
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
}
