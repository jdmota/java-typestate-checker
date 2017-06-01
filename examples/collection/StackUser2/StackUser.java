package examples.collection.StackUser2;

import examples.collection.Node;
import examples.collection.Stack;
import mungo.lib.Typestate;

@Typestate("StackUserProtocol")
class StackUser{
	private Stack s;

	StackUser() {
		s = new Stack();
		s.initialise(0);
	}

	void produce() {
		s.put(new Node(0));
		s.put(new Node(1));
	}

	void produce(int j) {
		int i = 0;
		do {
			s.put(new Node(i++));
		} while(i < j);
	}

	void consume() {
		loop: do {
			System.out.println(s.get().get() + " ");

			switch(s.isEmpty()) {
				case TRUE:
					break loop;

				case FALSE:
					continue loop;
			}
		} while(true);
	}

	void close() {
		s.close();
	}

	public static void main(String []args) {
		StackUser su = new StackUser();
		su.produce(20);
		su.consume();
		su.produce();
		su.produce();
		su.consume();
		su.close();
	}
}
