package tests

import org.junit.runners.Parameterized.Parameters
import java.io.File

private val defaultOpts = arrayOf("-Anomsgtext", "-AshowTypeInfo")

private const val dir1 = "config"

class MungoConfigTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir1,
  testFiles,
  defaultOpts.plus(arrayOf("-AconfigFile=tests/$dir1/mungo.config", "-Astubs=tests/$dir1/stubs", "-AstubWarnIfNotFound", "-Aignorejdkastub"))
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir1)
  }
}

private const val dir2 = "droppables"

class MungoDroppablesTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir2,
  testFiles,
  defaultOpts
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
  testFiles,
  defaultOpts
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
  testFiles,
  defaultOpts
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
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir5)
  }
}

private const val dir6 = "linearity"

class MungoLinearityTest(testFiles: List<File>) : MungoPerDirectoryTest(
  dir6,
  testFiles,
  arrayOf("-Anomsgtext")
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir6)
  }
}

private const val dir7 = "exceptions"

class MungoExceptions(testFiles: List<File>) : MungoPerDirectoryTest(
  dir7,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir7)
  }
}

private const val dir8 = "generics"

class MungoGenerics(testFiles: List<File>) : MungoPerDirectoryTest(
  dir8,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir8)
  }
}

private const val dir9 = "inference"

class MungoInference(testFiles: List<File>) : MungoPerDirectoryTest(
  dir9,
  testFiles,
  arrayOf("-Anomsgtext", "-AshowTypeInfo", "-AperformInference")
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir9)
  }
}
