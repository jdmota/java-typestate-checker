public class Main {

  public static void main() {
    Base b = new Derived();
    // :: warning: (b: State{Derived, HasNext} | State{Derived, Remove})
    while (b.hasNext()) {
      // :: warning: (b: State{Derived, Next} | State{Derived, NextRemove})
      b.next();
    }
  }

  // :: error: ([b] did not complete its protocol (found: State{Derived, Remove} | State{Derived, end}))
  public static void main2() {
    Base b = new Derived();
    // :: warning: (b: State{Derived, HasNext})
    if (b.hasNext()) {
      // :: warning: (b: State{Derived, Next})
      b.next();
    }
  }

}
