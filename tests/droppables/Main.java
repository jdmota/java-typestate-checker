public class Main {
	public static void main(String[] args) {
		MyComparator comparator = new MyComparator();
		// :: warning: (comparator: State{MyComparator, Start})
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    System.out.println(comparator.compare(10, 5));
	}
}
