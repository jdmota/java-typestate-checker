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
    return "";
  }

  public static void basicOk() {
    JavaIterator it = new JavaIterator();

    while (it.hasNext()) {
      it.next();
    }
  }

  public static void nullUse() {
    JavaIterator it = new JavaIterator();
    // :: error: (Cannot override because object has not ended its protocol)
    it = null;

    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void nullUse2() {
    JavaIterator it = new JavaIterator();

    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      it.next();
      // :: error: (Cannot override because object has not ended its protocol)
      it = null;
    }
  }

  public static void nullOk() {
    JavaIterator it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
    it = null;
  }

  public static void override() {
    JavaIterator it = new JavaIterator();
    if (it.hasNext()) {
      it.next();
    }
    // :: error: (Cannot override because object has not ended its protocol)
    it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void overrideOk() {
    JavaIterator it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
    it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void whileTrueOk() {
    // FIXME this error exists because "true" is not being considered
    // :: error: (Object did not complete its protocol)
    JavaIterator it = new JavaIterator();

    while (true) {
      if (it.hasNext()) {
        it.next();
      } else {
        break;
      }
    }
  }

  public static void whileTrueError() {
    // :: error: (Object did not complete its protocol)
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

  public static void assigment1() {
    JavaIterator it = new JavaIterator();
    @MungoState({"Next"}) JavaIterator it2 = it; // FIXME @MungoState getting ignored

    while (it2.hasNext()) {
      it2.next();
    }
  }

  public static void assigment2() {
    @MungoState({"Next"}) JavaIterator it3 = new JavaIterator(); // FIXME @MungoState getting ignored

    while (it3.hasNext()) {
      it3.next();
    }
  }

  public static void incompatibleArg() {
    JavaIterator it4 = new JavaIterator();
    // FIXME better error message
    // :: error: (argument.type.incompatible)
    use2(it4);
  }

  public static void validMove() {
    JavaIterator it5 = new JavaIterator();
    if (it5.hasNext()) {
      use2(it5);
    }
  }

  public static void wrongMove1() {
    JavaIterator it6 = new JavaIterator();
    // :: error: (Object did not complete its protocol)
    JavaIterator moved = it6;
    // :: error: (Cannot call hasNext on moved value)
    it6.hasNext();
  }

  public static void wrongMove2() {
    JavaIterator it6 = new JavaIterator();
    use1(it6);
    // :: error: (Cannot call hasNext on moved value)
    it6.hasNext();
  }

  public static void didNotComplete() {
    // :: error: (Object did not complete its protocol)
    JavaIterator it = new JavaIterator();
    if (it.hasNext()) {
      it.next();
    }
  }

  public static void didNotComplete2() {
    if (true) {
      // :: error: (Object did not complete its protocol)
      JavaIterator it10 = new JavaIterator();
      if (it10.hasNext()) {
        it10.next();
      }
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
