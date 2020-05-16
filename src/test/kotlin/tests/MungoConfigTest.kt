package tests

import org.junit.runners.Parameterized.Parameters
import java.io.File

private const val dir = "config"

class MungoConfigTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir,
  testFiles
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs
      get() = arrayOf(dir)
  }
}
