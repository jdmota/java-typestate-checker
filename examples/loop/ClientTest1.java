package demos.loop;

class ClientTest1 {
  	void test () {
  		LoopImpl loop = new LoopImpl();
  		out: do {
  			switch (loop.finished()) {
  			case FALSE:
  				continue out;
  			case TRUE:
  				;
  			}
  		} while(false);
  	}
}
