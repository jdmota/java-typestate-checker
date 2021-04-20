import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.State;

public class Main {

  public static void main1() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    Base b = d;
    // :: warning: (b: State "HasNext")
    while (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
  }

  public static void main2() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    if (d.hasNext()) {
      // :: warning: (d: State "Next")
      d.next();
    }
    // :: warning: (d: State "Remove" | Ended)
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
    Base b = d;
  }

  public static void main3() {
    Derived d = new Derived();
    // :: warning: (d: State "Remove" | State "HasNext")
    while (d.hasNext()) {
      // :: warning: (d: State "NextRemove" | State "Next")
      d.next();
    }
    // :: warning: (d: Ended)
    Base b = d;
  }

  public static void main4() {
    Base b = new Derived();
    // :: warning: (b: State "HasNext")
    while (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
  }

  public static void main5() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    helper(d);
  }

  public static void main6() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    if (d.hasNext()) {
      // :: warning: (d: State "Next")
      d.next();
    }
    // :: warning: (d: State "Remove" | Ended)
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
    helper(d);
  }

  public static void helper(@Requires("HasNext") Base b) {
    // :: warning: (b: State "HasNext")
    while (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
  }

  public static @State("HasNext") Base helper2() {
    return new Derived();
  }

  public static @State("HasNext") Base helper3() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    if (d.hasNext()) {
      // :: warning: (d: State "Next")
      d.next();
    }
    // :: warning: (d: State "Remove" | Ended)
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
    return d;
  }

  public static void main7() {
    Base b = (Base) new Derived();
    // :: warning: (b: State "HasNext")
    while (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
  }

  public static void main8() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    if (d.hasNext()) {
      // :: warning: (d: State "Next")
      d.next();
    }
    // :: warning: (d: State "Remove" | Ended)
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
    Base b = (Base) d;
  }

  public static void main9() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    Base b = (Base) d;
    // :: warning: (b: State "HasNext")
    Derived d2 = (Derived) b;
    // :: warning: (d2: State "Remove" | State "HasNext")
    while (d2.hasNext()) {
      // :: warning: (d2: State "NextRemove" | State "Next")
      d2.next();
    }
  }

  public static void main10() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    Base b = (Base) d;
    // :: warning: (b: State "HasNext")
    while (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
    // :: warning: (b: Ended)
    Derived d2 = (Derived) b;
  }

  public static void main11() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    Base b = (Base) d;
    // :: warning: (b: State "HasNext")
    if (b.hasNext()) {
      // :: warning: (b: State "Next")
      b.next();
    }
    // :: warning: (b: State "HasNext" | Ended)
    // :: error: (Object did not complete its protocol. Type: State "HasNext" | Ended)
    Derived d2 = (Derived) b;
    // this cast is actually safe, since "b" is left either in the initial state or end states
  }

  public static void main12() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    Base b = (Base) d;
    // :: warning: (b: State "HasNext")
    b.hasNext();
    // :: warning: (b: State "Next" | Ended)
    // :: error: Down-casting not allowed. Expected State "HasNext" | Ended but got State "Next" | Ended
    Derived d2 = (Derived) b;
  }

  // Testing casts to objects without protocol (i.e. object that can be shared)

  public static void main13() {
    Derived d = new Derived();
    // :: warning: (d: State "HasNext")
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    // :: error: (Up-casting to a type with no protocol is not allowed)
    Object alias = d;
  }

}
