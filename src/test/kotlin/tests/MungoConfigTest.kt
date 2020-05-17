package tests

import org.junit.runners.Parameterized.Parameters
import java.io.File

private const val dir = "config"

class MungoConfigTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir,
  testFiles,
  arrayOf("-Astubs=tests/$dir/stubs", "-AstubWarnIfNotFound", "-Aignorejdkastub")
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir)
  }
}
