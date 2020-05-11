package demos.loop;

class ClientTest4 {
    void test() {
        LoopImpl loop = new LoopImpl();
        out:
        do {
            switch (loop.finished()) {
                case FALSE:
                    continue out;
                case TRUE:
                    break out;
            }
        } while (false);
    }
}
