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

private const val dir2 = "droppables"

class MungoDroppablesTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir2,
  testFiles
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir2)
  }
}

private const val dir3 = "resolution"

class MungoResolutionTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir3,
  testFiles
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir3)
  }
}

private const val dir4 = "mungo"

class MungoTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir4,
  testFiles
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir4)
  }
}

private const val dir5 = "linked-list"

class MungoLinkedListTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir5,
  testFiles
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir5)
  }
}
