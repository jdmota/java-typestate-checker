public class Main {
  public static void main() {
    Derived d = new Derived();
    // :: warning: (d: State "Start")
    if (d.hasNext()) {
      // :: warning: (d: State "Next")
      d.next();
      // :: warning: (d: State "Remove")
      if (d.hasNext()) {
        // :: warning: (d: State "NextRemove")
        d.remove();
        // :: warning: (d: State "Next")
        d.next();
        // :: warning: (d: State "Remove")
        d.remove();
      }
    }
    // :: warning: (d: State "Start")
    Base b = d; // allowed upcast
    // :: warning: (b: State "Start")
    if (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
    // :: warning: (b: State "Start")
    Derived d2 = (Derived) b; // allowed downcast
  }
}
