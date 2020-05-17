package tests

import org.junit.runners.Parameterized.Parameters
import java.io.File

private const val dir = "mungo"

class MungoTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir,
  testFiles
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir)
  }
}
