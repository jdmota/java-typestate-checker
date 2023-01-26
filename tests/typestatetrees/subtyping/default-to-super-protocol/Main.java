public class Main {

  public static void main1() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    while (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
  }

  // :: error: ([d] did not complete its protocol (found: State{Derived, HasNext}))
  public static void main2() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    d.hasNext();
    // :: warning: (d: State{Derived, Next} | State{Derived, end})
    // :: error: (Cannot call [next] on State{Derived, Next} | State{Derived, end})
    d.next();
  }

}
