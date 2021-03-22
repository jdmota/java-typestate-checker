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
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
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
    }
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
    helper(d);
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
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
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
    // :: error: [assignment.type.incompatible] found: Ended Base; required: State "HasNext" | State "Next" Base
    // this error is because new variables do not expect "ended" objects
    // :: error: (Up-casting not allowed. Expected State "HasNext" | Ended but got State "Remove" | Ended)
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
    // :: error: [assignment.type.incompatible] found: Ended Base; required: State "HasNext" | State "Next" | State "Remove" | State "NextRemove" Derived
    // this error is because new variables do not expect "ended" objects
    Derived d2 = (Derived) b;
  }

  public static void main11() {
    Derived d = new Derived();
    Base b = (Base) d;
    if (b.hasNext()) {
      b.next();
    }
    // :: error: [assignment.type.incompatible]
    // this error is because new variables do not expect "ended" objects
    Derived d2 = (Derived) b;
    // this cast is actually safe, since "b" is left either in the initial state or end states
  }

  public static void main12() {
    Derived d = new Derived();
    Base b = (Base) d;
    b.hasNext();
    // :: error: [assignment.type.incompatible]
    // this error is because new variables do not expect "ended" objects
    // :: error: Down-casting not allowed. Expected State "HasNext" | Ended but got State "Next" | Ended
    Derived d2 = (Derived) b;
  }

}
