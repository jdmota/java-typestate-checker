import org.extendj.ast.TypestateChecker;
import org.extendj.JavaChecker;

import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;

class TypestateMain {
	JavaChecker jc;
	TypestateChecker tc;

	private String[] files;
	private String[] mungoFiles;

	private boolean printErrors = true;
	private boolean verbose = false;
	private boolean printInference = false;

	private final int DEFAULT = 0x111;
	private final int TYPESTATE = 0x01;
	private final int JAVA18 = 0x10;

	private int mode = DEFAULT;

	TypestateMain() {
		jc = new JavaChecker();
		tc = new TypestateChecker();
	}

	private boolean compile() {
		boolean j = true, t = true;
		if((mode & JAVA18) != 0) {
			if(verbose)
				System.out.println("Checking java 1.8.");
			j = jc.compile(files);
		}

		if(!j)
			return false;

		if((mode & TYPESTATE) != 0) {
			if(verbose)
				System.out.println("Typestate check.");
			t = tc.compile(mungoFiles);
			if((tc.hasErrors() || tc.hasWarnings()) && printErrors) {
				if(verbose)
					System.out.println("Print errors and warnings.");
				tc.printErrors();
			}
		}

		return j & t;
	}

	private void setMode(int m) {
		if(mode == DEFAULT)
			mode = m;
		else
			mode |= m;
	}

	void processArgs(String[] args) {
		ArrayList<String> arguments = new ArrayList<String>();

		for(int i = 0; i < args.length; i++) {
			if(args[i].equals("-Verbose") || args[i].equals("-verbose") || args[i].equals("-v")) {
				verbose = true;
				tc.setVerbose();
			}
			else if(args[i].equals("-Output") || args[i].equals("output") || args[i].equals("-o")) {
				if(i + 1 >= args.length)
					; //TODO error
				else {
					try {
						tc.setOutputStream(new PrintStream(args[++i]));
					}
					catch (FileNotFoundException e) {
						System.err.println(e);
						System.exit(1);
					}
				}
			}
			else if(args[i].equals("-Typestate") || args[i].equals("-typestate") || args[i].equals("-t"))
				setMode(TYPESTATE);
			else if(args[i].equals("-Java18") || args[i].equals("-java18") || args[i].equals("-j"))
				setMode(JAVA18);
			else if(args[i].equals("-printInference") || args[i].equals("-pi")) {
				printInference = true;
				tc.setPrintInference();
			}
			else
				arguments.add(args[i]);
		}

		this.files = arguments.toArray(new String[arguments.size()]);
		if(arguments.contains("-cp")) {
			arguments.remove(arguments.indexOf("-cp") + 1);
			arguments.remove(arguments.indexOf("-cp"));
		}
		if(arguments.contains("-classpath")) {
			arguments.remove(arguments.indexOf("-classpath") + 1);
			arguments.remove(arguments.indexOf("-classpath"));
		}

		this.mungoFiles = arguments.toArray(new String[arguments.size()]);

	}

	public static void main(String [] args) {
		if(args.length == 0) {
			usage();
			return;
		}
		TypestateMain m = new TypestateMain();
		m.processArgs(args);
		m.compile();
	}


	private static void usage() {
		System.out.println();
		System.out.println("\tusage: java TypestateMain [flags] files");
		System.out.println();
		System.out.println("flags:");
		System.out.println();
		System.out.print("-Typestate -typestate -t:");
		System.out.println("\tPerform only typechecking.");
		System.out.print("-JAVA18 -JAVA18 -j:");
		System.out.println("\t\tPerform only java1.8 checking.");
		System.out.println("Note if you put both of the above flags you get both Typestate and Java checks.");
		System.out.println();
		System.out.print("-Verbose -verbose -v:");
		System.out.println("\t\tPrint the steps the typestate typechecker does.");
		System.out.print("-printInference -pi:");
		System.out.println("\t\tPrints all the infered types.");
	}
}
