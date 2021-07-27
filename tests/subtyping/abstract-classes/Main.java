public class Main {

  public static void main() {
    Base b = new Derived();
    // :: warning: (b: State{Base, HasNext})
    while (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
  }

  // :: error: ([b] did not complete its protocol (found: State{Base, HasNext} | State{Base, end}))
  public static void main2() {
    Base b = new Derived();
    // :: warning: (b: State{Base, HasNext})
    if (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
  }

}
