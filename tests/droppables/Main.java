public class Main {
	public static void main(String[] args) {
		MyComparator comparator = new MyComparator();
		// :: warning: (comparator: State "Start")
    System.out.println(comparator.compare(10, 5));
	}
}
