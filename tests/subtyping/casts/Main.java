import jatyc.lib.Requires;
import jatyc.lib.Ensures;

public class Main {

  public static void upcastBase(Base base) {

  }

  public static void upcastObject(Object obj) {
    // :: warning: (obj: Shared{java.lang.Object})
    if (obj instanceof Base) {
      // :: warning: (obj: Shared{Base})
      Base b = (Base) obj;
    }
  }

  public static void main1() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = d;
    // :: warning: (b: State{Base, HasNext})
    while (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
  }

  public static void main2() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    // :: error: (Incompatible parameter: cannot cast from State{Derived, Remove} | State{Derived, end} to Shared{Base})
    upcastBase(d);
  }

  public static void main3() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext} | State{Derived, Remove})
    while (d.hasNext()) {
      // :: warning: (d: State{Derived, Next} | State{Derived, NextRemove})
      d.next();
    }
    // :: warning: (d: State{Derived, end})
    upcastBase(d);
  }

  public static void main4() {
    Base b = new Derived();
    // :: warning: (b: State{Base, HasNext})
    while (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
  }

  public static void main5() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    helper(d);
  }

  public static void main6() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    // :: error: (Incompatible parameter: cannot cast from State{Derived, Remove} | State{Derived, end} to State{Base, HasNext})
    helper(d);
  }

  public static void helper(@Requires("HasNext") Base b) {
    // :: warning: (b: State{Base, HasNext})
    while (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
  }

  public static @Ensures("HasNext") Base helper2() {
    return new Derived();
  }

  public static @Ensures("HasNext") Base helper3() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    // :: error: (Incompatible return value: cannot cast from State{Derived, Remove} | State{Derived, end} to State{Base, HasNext})
    return d;
  }

  public static void main7() {
    Base b = (Base) new Derived();
    // :: warning: (b: State{Base, HasNext})
    while (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
  }

  public static void main8() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    // :: error: (Incompatible parameter: cannot cast from State{Derived, Remove} | State{Derived, end} to Shared{Base})
    upcastBase(d);
  }

  public static void main9() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Base, HasNext})
    // :: warning: (Unsafe cast)
    Derived d2 = (Derived) b;
    // :: warning: (d2: State{Derived, HasNext} | State{Derived, Remove})
    while (d2.hasNext()) {
      // :: warning: (d2: State{Derived, Next} | State{Derived, NextRemove})
      d2.next();
    }
  }

  public static void main10() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Base, HasNext})
    while (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
    // :: warning: (b: State{Base, end})
    // :: warning: (Unsafe cast)
    Derived d2 = (Derived) b;
  }

  // :: error: ([d2] did not complete its protocol (found: State{Derived, HasNext} | State{Derived, end}))
  public static void main11() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Base, HasNext})
    if (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
    // :: warning: (b: State{Base, HasNext} | State{Base, end})
    // :: warning: (Unsafe cast)
    Derived d2 = (Derived) b;
  }

  public static void main12() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Base, HasNext})
    b.hasNext();
    // :: warning: (b: State{Base, Next} | State{Base, end})
    // :: error: (Cannot perform cast from State{Base, Next} | State{Base, end} to Shared{Derived} | State{Derived, ?} | Null)
    Derived d2 = (Derived) b;
  }

  public static void main13() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    // :: error: (Cannot assign: cannot cast from State{Derived, HasNext} to Shared{java.lang.Object} | Null)
    Object alias = d;
  }

  public static void main14() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    // :: error: (Cannot perform cast from State{Derived, HasNext} to Shared{java.lang.Object} | Null)
    upcastObject((Object) d);
  }

  public static void main15(@Requires("HasNext") Base b) {
    // :: warning: (b: State{Base, HasNext})
    if (b instanceof Derived) {
      // :: warning: (b: State{Derived, HasNext} | State{Derived, Remove})
      while (b.hasNext()) {
        // :: warning: (b: State{Derived, Next} | State{Derived, NextRemove})
        b.next();
      }
    } else {
      // :: warning: (b: State{Base, HasNext})
      while (b.hasNext()) {
        // :: warning: (b: State{Base, Next})
        b.next();
      }
    }
  }

  public static void main16() {
    Object obj = new Object();
    // :: warning: (obj: Shared{java.lang.Object})
    if (obj instanceof Base) {
      // :: warning: (obj: Shared{Base})
      Base b = (Base) obj;
    }
  }

  public static void main17() {
    Object obj = null;
    if (1 < 5) {
      // :: warning: (obj: Null)
      // :: error: (Cannot assign: cannot cast from State{Base, HasNext} to Shared{java.lang.Object} | Null)
      obj = new Base();
    } else {
      // :: warning: (obj: Null)
      obj = new String();
    }
    // :: warning: (obj: Shared{java.lang.Object})
    if (obj instanceof Base) {
      // :: warning: (obj: Shared{Base})
      Base b = (Base) obj;
    } else {
      // :: warning: (obj: Shared{java.lang.Object})
      // :: warning: (Unsafe cast)
      String str = (String) obj;
      // :: warning: (str: Shared{java.lang.String})
      str.toUpperCase();
    }
  }

  // :: error: ([b] did not complete its protocol (found: Shared{Derived} | State{Base, HasNext}))
  public static void main18(@Requires("HasNext") Base b) {
    // :: warning: (b: State{Base, HasNext})
    if (b instanceof Derived) {
      // :: warning: (b: State{Derived, HasNext})
      Derived d = (Derived) b;
      // :: warning: (d: State{Derived, HasNext})
      // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
      // :: error: (Incompatible parameter: cannot cast from State{Derived, HasNext} to Shared{java.lang.Object} | Null)
      System.out.println(d);
    }
  }

}
