package demos.Traversal;

class Node implements java.io.Serializable {
	private Node left, right;
	private int data;

	Node(Node l, Node r, int d) {
		left = l;
		right = r;
		data = d;
	}

	Node left() {
		return left;
	}

	Node right() {
		return right;
	}

	int get() {
		return data;
	}
}
