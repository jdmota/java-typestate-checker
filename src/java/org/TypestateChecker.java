package org.extendj;

import java.util.*;
import java.io.*;

import org.extendj.ast.Frontend;
import org.extendj.ast.Program;
import org.extendj.ast.Options;


public class TypestateChecker extends Frontend {

  /**
   * Default entry point.
   * @param args command-line arguments
   */
  public static void main(String args[]) {
    int exitCode = new TypestateChecker().run(args);
    if (exitCode != 0) {
      System.exit(exitCode);
    }
  }

  public TypestateChecker() {
    super("TypestateChecker", "1.0.0");
  }

  public int run(String[] args) {
    int exitCode = run(args, Program.defaultBytecodeReader(), Program.defaultJavaParser());
    Options options = program.options();

    program.compile(program.options().files().toArray(new String[program.options().files().size()]));
    for(int i = 0; i < program.getNumCompilationUnit(); i++){
      processCompilationUnit(program.getCompilationUnit(i));
    }
    return exitCode;
  }

  protected void initOptions() {
    super.initOptions();
    Options options = program.options();
    options.addKeyOption("-v");
    options.addKeyOption("-pi");
    options.addKeyOption("-j");
  }


  protected void printUsage() {
      printVersion();
      System.out.println(
          "Usage: java -jar mungo.jar <options> <source files>\n" +
          "  -v                        Print the steps the typestate typechecker does\n" +
          "  -classpath <path>         Specify where to find user class files\n" +
          "  -sourcepath <path>        Specify where to find input source files\n" +
          "  -bootclasspath <path>     Override location of bootstrap class files\n" +
          "  -extdirs <dirs>           Override location of installed extensions\n" +
          "  -j                        Perform only java1.4 checking\n" +
          "  -pi                       Prints all the infered types \n" +
          "  -help                     Print a synopsis of standard options\n" +
          "  -version                  Print version information\n"
          );
    }


}
