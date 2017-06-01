package examples.collection;

public class Node {
	private int i;
	private Node next;

	public Node(int i) {
		this.i = i;
		next = null;
	}

	public void set(int i) {
		this.i = i;
	}

	public String get() {
		return "The number of this Node is: " + i;
	}

	public Node next(Node in) {
		next = in;
		return this;
	}

	public Node next() {
		return next;
	}
}
