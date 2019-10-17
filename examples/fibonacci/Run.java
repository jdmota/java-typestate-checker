package examples.fibonacci;


class Run {
	public static void main(String args[]) {
		int index = parseArgs(args);

		Thread t1 = new Thread(new NodeA(2001, index));
		Thread t2 = new Thread(new NodeB(2001));

		t1.start();
		t2.start();
	}

	static private int parseArgs(String args[]) {
		int index = 0;
		if (args.length > 0) {
			try {
				index = Integer.parseInt(args[0]);
			} catch (NumberFormatException e) {
		//		System.err.println("Argument" + args[0] + " must be an integer.");
		//		System.exit(1);
			}
		}
		return index;
	}
}
