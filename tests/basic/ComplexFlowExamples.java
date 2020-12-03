import org.checkerframework.checker.jtc.lib.Typestate;

class ComplexFlowExamples {
  // https://github.com/typetools/checker-framework/issues/3267
  public static void example1() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    it.hasNext();
    if (true) {
      // :: warning: (it: State "Next" | Ended)
      // :: error: (Cannot call next on ended protocol)
      it.next();
    } else {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  public static void example2() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    it.hasNext();
    if (!true) {
      // :: warning: (it: Bottom)
      it.next();
    } else {
      // :: warning: (it: State "Next" | Ended)
      // :: error: (Cannot call next on ended protocol)
      it.next();
    }
  }

  public static void example3() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    it.hasNext();
    if (!!true) {
      // :: warning: (it: State "Next" | Ended)
      // :: error: (Cannot call next on ended protocol)
      it.next();
    } else {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  public static void example4() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    it.hasNext();
    if (!false) {
      // :: warning: (it: State "Next" | Ended)
      // :: error: (Cannot call next on ended protocol)
      it.next();
    } else {
      // :: warning: (it: Bottom)
      it.next();
    }
  }
}
