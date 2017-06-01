package examples.collection.StackUser;

import examples.collection.Node;
import examples.collection.Stack;
import mungo.lib.Typestate;

@Typestate("StackUserProtocol")
class StackUser{
	Stack produce(Stack s) {
		s.put(new Node(0));
		s.put(new Node(1));
		s.put(new Node(2));
		s.put(new Node(3));
		s.put(new Node(4));
		return s;
	}

	Stack produce(Stack s, int j) {
		int i = 0;
		do {
			s.put(new Node(i++));
		} while(i < j);

		return s;
	}

	Stack consume(Stack s) {
		loop: do {
			System.out.println(s.get().get() + " ");

			switch(s.isEmpty()) {
				case TRUE:
					break loop;

				case FALSE:
					continue loop;
			}
		} while(true);

		return s;
	}

	void close() {
	}

	public static void main(String []args) {
		Stack s = new Stack();
		s.initialise(0);

		StackUser su = new StackUser();
		s = su.produce(s);
		s = su.produce(s);
		s = su.consume(s);

		s = su.produce(s, 60);
		s = su.consume(s);

		s.close();
		su.close();
	}
}
