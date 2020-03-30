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

  public static void basicOk() {
    JavaIterator it = new JavaIterator();

    while (it.hasNext()) {
      it.next();
    }
  }

  public static void nullUse() {
    JavaIterator it = new JavaIterator();
    // :: error: (Cannot assign null because object has not ended its protocol)
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
      // :: error: (Cannot assign null because object has not ended its protocol)
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

  public static void whileTrueOk() {
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
