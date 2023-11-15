package tests

import org.junit.runners.Parameterized.Parameters
import java.io.File

val ignore = listOf("linked-list", "generics")
val only = emptyList<String>()

private val defaultOptsNoTypeInfo = arrayOf("-Anomsgtext", "-AtypestateTrees=disable")
private val defaultOpts = defaultOptsNoTypeInfo.plus("-AshowTypeInfo")

private const val dir0 = "debug"

// A folder where we can make tests and narrow down an issue
class DebugTests(testFiles: List<File>) : PerDirectoryTest(
  dir0,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir0)
  }
}

private const val dir1 = "basic"

class BasicTests(testFiles: List<File>) : PerDirectoryTest(
  dir1,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir1)
  }
}

private const val dir2 = "config"

class ConfigTest(testFiles: List<File>) : PerDirectoryTest(
  dir2,
  testFiles,
  defaultOpts.plus(arrayOf("-AconfigFile=tests/$dir2/jtc.config", "-Astubs=tests/$dir2/stubs", "-AstubWarnIfNotFound", "-Aignorejdkastub"))
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir2)
  }
}

private const val dir3 = "droppables"

class DroppablesTest(testFiles: List<File>) : PerDirectoryTest(
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

private const val dir4 = "resolution"

class ResolutionTest(testFiles: List<File>) : PerDirectoryTest(
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
  defaultOptsNoTypeInfo
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

private const val dir10 = "assignments"

class AssignmentsTests(testFiles: List<File>) : PerDirectoryTest(
  dir10,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir10)
  }
}

private const val dir11 = "suppress-warnings"

class SuppressWarningsTests(testFiles: List<File>) : PerDirectoryTest(
  dir11,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir11)
  }
}

private const val dir12 = "class-analysis"

class ClassAnalysisTests(testFiles: List<File>) : PerDirectoryTest(
  dir12,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir12)
  }
}

private const val dir13 = "complex-flow"

class ComplexFlowTests(testFiles: List<File>) : PerDirectoryTest(
  dir13,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir13)
  }
}

private const val dir14 = "typestatetrees"

class TypestateTreesTests(testFiles: List<File>) : PerDirectoryTest(
  dir14,
  testFiles,
  arrayOf("-Anomsgtext", "-AtypestateTrees=enable", "-AshowTypeInfo")
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir14)
  }
}

private const val dir15 = "cfg"

class CFGTests(testFiles: List<File>) : PerDirectoryTest(
  dir15,
  testFiles,
  defaultOpts
) {
  companion object {
    @JvmStatic
    @get:Parameters
    val testDirs = arrayOf(dir15)
  }
}
