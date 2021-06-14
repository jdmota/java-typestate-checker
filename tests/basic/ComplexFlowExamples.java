import jatyc.lib.Typestate;

// https://github.com/typetools/checker-framework/issues/3267

class ComplexFlowExamples {
  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void example1() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    it.hasNext();
    if (true) {
      // :: warning: (it: State{JavaIterator, Next} | State{JavaIterator, end})
      // :: error: (Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end})
      it.next();
    } else {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void example2() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    it.hasNext();
    if (!true) {
      // :: warning: (it: Bottom)
      it.next();
    } else {
      // :: warning: (it: State{JavaIterator, Next} | State{JavaIterator, end})
      // :: error: (Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end})
      it.next();
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void example3() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    it.hasNext();
    if (!!true) {
      // :: warning: (it: State{JavaIterator, Next} | State{JavaIterator, end})
      // :: error: (Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end})
      it.next();
    } else {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void example4() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    it.hasNext();
    if (!false) {
      // :: warning: (it: State{JavaIterator, Next} | State{JavaIterator, end})
      // :: error: (Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end})
      it.next();
    } else {
      // :: warning: (it: Bottom)
      it.next();
    }
  }
}
