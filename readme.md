How to run:

-
		java -jar mungo.jar

	give you a description of the usage of the mungo typechecker.

-
		java -jar mungo.jar [options] [FILES]

	performs type check on the files specified by FILES with the options specified by [options]

Examples:
	type checks and produces .java files for the corresponding .mungo file

Collection examples
-
		java -jar mungo.jar examples/collection/Stack.mungo
-
		java -jar mungo.jar examples/collection/StackUser/StackUser.mungo
-
		java -jar mungo.jar examples/collection/StackUser2/StackUser.mungo



Hello World examples
-
		java -jar mungo.jar examples/TwoParties/Main.mungo
-
		java -jar mungo.jar examples/ThreeParties/Main.mungo
