import jatyc.lib.Requires;
import jatyc.lib.Ensures;

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
    if (d.hasNext()) {
      d.next();
      helper(d);
    }
  }

  public static void helper(@Requires("HasNext") Base b) {
    while (b.hasNext()) {
      b.next();
    }
  }

  public static @Ensures("HasNext") Base helper2() {
    return new Derived();
  }

  public static @Ensures("HasNext") Base helper3() {
    Derived d = new Derived();
    if (d.hasNext()) {
      d.next();
    }
    return d;
  }

  public static void main7() {
    Base b = (Base) new Derived();
    while (b.hasNext()) {
      b.next();
    }
  }

  public static void main8() {
    Derived d = new Derived();
    if (d.hasNext()) {
      d.next();
    }
    Base b = (Base) d;
  }

  public static void main9() {
    Derived d = new Derived();
    Base b = (Base) d;
    Derived d2 = (Derived) b;
    while (d2.hasNext()) {
      d2.next();
    }
  }

  public static void main10() {
    Derived d = new Derived();
    Base b = (Base) d;
    while (b.hasNext()) {
      b.next();
    }
    Derived d2 = (Derived) b;
  }

  public static void main11() {
    Derived d = new Derived();
    Base b = (Base) d;
    if (b.hasNext()) {
      b.next();
    }
    Derived d2 = (Derived) b;
  }

  public static void main12() {
    Derived d = new Derived();
    Base b = (Base) d;
    b.hasNext();
    Derived d2 = (Derived) b;
  }

}
