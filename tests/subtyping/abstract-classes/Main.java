public class Main {

  public static void main() {
    Base b = new Derived();
    // :: warning: (b: State "HasNext")
    while (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
  }

  public static void main2() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext" | Ended)
    Base b = new Derived();
    // :: warning: (b: State "HasNext")
    if (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
  }

}
