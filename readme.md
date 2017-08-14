**How to run:**

-
		java -jar mungo.jar

	gives you a description of the usage of the mungo typechecker.

-
		java -jar mungo.jar -classpath .:bin/mungo.jar [options] [FILES]

	performs type check on the files specified by FILES with the options specified by [options]

Examples:
	type checks `.java` and `.protocol` files

Collection examples
-
		java -jar bin/mungo.jar -classpath .:bin/mungo.jar examples/collection/Stack.java
-
		java -jar bin/mungo.jar -classpath .:bin/mungo.jar examples/collection/StackUser/StackUser.java
-
        java -jar bin/mungo.jar -classpath .:bin/mungo.jar examples/collection/StackUser2/StackUser.java


Hello World examples
-
		java -jar mungo.jar -classpath .:bin/mungo.jar examples/TwoParties/Main.java

-
		java -jar mungo.jar -classpath .:bin/mungo.jar examples/ThreeParties/Main.java

If no errors are detected the program can be compiled and run using `javac,
like any other Java program.

**The tool jar must be added as an external library to the project.**
