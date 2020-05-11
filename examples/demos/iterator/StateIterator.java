package demos.iterator;

import java.util.Iterator;

@Typestate("StateIteratorProtocol")
class StateIterator {
	Iterator iter;
	public StateIterator(Iterator i) {
		iter = i;
	}

	public Object next() {
		return iter.next();
	}

	public BooleanEnum hasNext() {
		if(iter.hasNext())
			return BooleanEnum.TRUE;
		return BooleanEnum.FALSE;
	}

	public void remove() {
		iter.remove();
	}
}
