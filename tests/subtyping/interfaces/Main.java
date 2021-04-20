public class Main {

  public static void main() {
    // :: error: (Up-casting to a type with no protocol is not allowed)
    Base b = new Derived();
    // :: warning: (b: Bottom)
    while (b.hasNext()) {
      // :: warning: (b: Bottom)
      b.next();
    }
  }

  public static void main2() {
    // :: error: (Up-casting to a type with no protocol is not allowed)
    Base b = new Derived();
    // :: warning: (b: Bottom)
    if (b.hasNext()) {
      // :: warning: (b: Bottom)
      b.next();
    }
  }

}
