import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.State;

public class Main {

  public static void main1() {
    Derived d = new Derived();
    Base b = d;
    while (b.hasNext()) {
      b.next();
    }
  }

  public static void main2() {
    Derived d = new Derived();
    if (d.hasNext()) {
      d.next();
    }
    Base b = d;
    // Error: cannot up-cast
    // Error: did not complete the protocol
  }

  public static void main3() {
    Derived d = new Derived();
    while (d.hasNext()) {
      d.next();
    }
    Base b = d;
  }

  public static void main4() {
    Base b = new Derived();
    while (b.hasNext()) {
      b.next();
    }
  }

  public static void main5() {
    Derived d = new Derived();
    helper(d);
  }

  public static void main6() {
    Derived d = new Derived();
    helper(d);
  }

  public static void main7() {
    Derived d = new Derived();
    if (d.hasNext()) {
      d.next();
    }
    helper(d);
    // Error: cannot up-cast
  }

  public static void helper(@Requires("HasNext") Base b) {
    while (b.hasNext()) {
      b.next();
    }
  }

  public static @State("HasNext") Base helper2() {
    return new Derived();
  }

  public static @State("HasNext") Base helper3() {
    Derived d = new Derived();
    if (d.hasNext()) {
      d.next();
    }
    return d;
    // Error: cannot up-cast
  }

}
