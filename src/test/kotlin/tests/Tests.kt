package tests

import org.junit.runners.Parameterized.Parameters
import java.io.File

// TODO we now need support for interfaces for "config" tests to work
val ignore = listOf("config", "generics", "inference")
val only = emptyList<String>()

private val defaultOpts = arrayOf("-Anomsgtext", "-AshowTypeInfo")

private const val dir1 = "config"

class ConfigTest(testFiles: List<File>) : PerDirectoryTest(
  dir1,
  testFiles,
  defaultOpts.plus(arrayOf("-AconfigFile=tests/$dir1/jtc.config", "-Astubs=tests/$dir1/stubs", "-AstubWarnIfNotFound", "-Aignorejdkastub"))
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir1)
  }
}

private const val dir2 = "droppables"

class DroppablesTest(testFiles: List<File>) : PerDirectoryTest(
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

class ResolutionTest(testFiles: List<File>) : PerDirectoryTest(
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

private const val dir4 = "basic"

class BasicTests(testFiles: List<File>) : PerDirectoryTest(
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

class LinkedListTest(testFiles: List<File>) : PerDirectoryTest(
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

class LinearityTest(testFiles: List<File>) : PerDirectoryTest(
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

class ExceptionsTest(testFiles: List<File>) : PerDirectoryTest(
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

class GenericsTest(testFiles: List<File>) : PerDirectoryTest(
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

private const val dir9 = "subtyping"

class SubtypingTest(testFiles: List<File>) : PerDirectoryTest(
  dir9,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir9)
  }
}

private const val dir10 = "inference"

class InferenceTest(testFiles: List<File>) : PerDirectoryTest(
  dir10,
  testFiles,
  arrayOf("-Anomsgtext", "-AshowTypeInfo", "-AperformInference")
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir10)
  }
}
