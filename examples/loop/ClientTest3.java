package demos.loop;

class ClientTest3 {
	void test2() {
		test(new LoopImpl());
	}

  	void test (LoopImpl loop) {
		switch(loop.finished()) {
			case FALSE:
				test(loop);
			case TRUE:
				break;
		}
  	}
}
