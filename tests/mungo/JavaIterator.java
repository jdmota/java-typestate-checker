import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;

import java.util.Iterator;

// FIXME fix error location

@MungoTypestate("JavaIterator.protocol")
// :: warning: (JavaIterator.protocol has no WrongName state)
// :: warning: (State end is final. Will have no effect in @MungoState)
class JavaIterator implements Iterator<Object> {

  @Override
  public boolean hasNext() {
    return false;
  }

  @Override
  public Object next() {
    return null;
  }

  public static void main(String[] args) {
    JavaIterator it = new JavaIterator();

    while (it.hasNext()) {
      it.next();
    }
  }

  public static void main2(String[] args) {
    JavaIterator it = new JavaIterator();
    it = null;

    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void main3(String[] args) {
    JavaIterator it = new JavaIterator();

    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      it.next();
      it = null;
    }
  }

  public static void main4(String[] args) {
    JavaIterator it = new JavaIterator();

    while (true) {
      if (it.hasNext()) {
        it.next();
      } else {
        break;
      }
    }
  }

  public static void main5(String[] args) {
    JavaIterator it = new JavaIterator();

    while (true) {
      if (!it.hasNext()) {
        // :: error: (Cannot call next on ended protocol)
        it.next();
      } else {
        break;
      }
    }
  }

  public static void main6(String[] args) {
    JavaIterator it = new JavaIterator();
    @MungoState({"Next"}) JavaIterator it2 = it; // FIXME @MungoState getting ignored

    while (it2.hasNext()) {
      it2.next();
    }
  }

  public static void main7(String[] args) {
    @MungoState({"Next"}) JavaIterator it3 = new JavaIterator(); // FIXME @MungoState getting ignored

    while (it3.hasNext()) {
      it3.next();
    }
  }

  public static void main8(String[] args) {
    JavaIterator it4 = new JavaIterator();
    // FIXME better error message
    // :: error: (argument.type.incompatible)
    use2(it4);
  }

  public static void main9(String[] args) {
    JavaIterator it5 = new JavaIterator();
    if (it5.hasNext()) {
      use2(it5);
    }
  }

  public static void use1(JavaIterator it) {
    // :: error: (Cannot call hasNext on state Next (got: HasNext, Next))
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void use2(@MungoState({"Next"}) JavaIterator it) {
    it.next();
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void use3(@MungoState({"Next", "WrongName", "end"}) JavaIterator it) {
    it.next();
    while (it.hasNext()) {
      it.next();
    }
  }

}
