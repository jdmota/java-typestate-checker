public class Main {

  public static void main1() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    while (d.hasNext()) {
      // :: warning: (d: State "Next")
      d.next();
    }
  }

  public static void main2() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    d.hasNext();
    // :: warning: (d: State "Next" | Ended)
    // :: error: (Cannot call next on ended protocol)
    d.next();
  }

}
