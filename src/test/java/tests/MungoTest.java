import java.io.File;
import java.util.List;

import org.checkerframework.checker.mungo.MungoChecker;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized.Parameters;

/**
 * Test runner for tests of the Mungo Checker.
 *
 * <p>Tests appear as Java files in the {@code tests/mungo} folder. To add a new test case,
 * create a Java file in that directory. The file contains "// ::" comments to indicate expected
 * errors and warnings; see
 * https://github.com/typetools/checker-framework/blob/master/checker/tests/README .
 */
public class MungoTest extends CheckerFrameworkPerDirectoryTest {
  public MungoTest(List<File> testFiles) {
    super(
      testFiles,
      MungoChecker.class,
      "mungo",
      "-Anomsgtext");
  }

  @Parameters
  public static String[] getTestDirs() {
    return new String[]{"mungo"};
  }
}
