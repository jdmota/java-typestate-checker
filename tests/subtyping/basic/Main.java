public class Main {
  public static void main() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, Start})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
      // :: warning: (d: State{Derived, Remove})
      if (d.hasNext()) {
        // :: warning: (d: State{Derived, NextRemove})
        d.remove();
        // :: warning: (d: State{Derived, Next})
        d.next();
        // :: warning: (d: State{Derived, Remove})
        d.remove();
      }
    }
    // :: warning: (d: State{Derived, Start})
    Base b = d;
    // :: warning: (b: State{Derived, Start})
    if (b.hasNext()) {
      // :: warning: (b: State{Derived, Next})
      b.next();
    }
    // :: warning: (b: State{Derived, Start})
    Derived d2 = (Derived) b;
  }
}
