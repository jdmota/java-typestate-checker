import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.Iterator;
import java.util.function.Supplier;

@MungoTypestate("JavaIterator.protocol")
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

  public static void initializedNull() {
    // :: error: (assignment.type.incompatible)
    JavaIterator it = null;
    it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void initializedNullOk() {
    @MungoNullable JavaIterator it = null;
    it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void refineNull(@MungoNullable JavaIterator it) {
    if (it != null) {
      while (it.hasNext()) {
        it.next();
      }
    }
  }

  public static JavaIterator refineNull2(@MungoNullable JavaIterator it) {
    if (it instanceof JavaIterator) {
      return it;
    }
    throw new RuntimeException("");
  }

  public static void refineNull3(@MungoNullable JavaIterator it) {
    if (it == null) {
      // :: error: (Cannot call hasNext on null)
      it.hasNext();
    } else {
      while (it.hasNext()) {
        it.next();
      }
    }
  }

  public static @MungoState({"HasNext"}) JavaIterator correctReturn(@MungoState({"Next"}) JavaIterator it) {
    it.next();
    return it;
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
    // :: error: (assignment.type.incompatible)
    @MungoState({"Next"}) JavaIterator it2 = it;

    while (it2.hasNext()) {
      it2.next();
    }
  }

  public static void assigment2() {
    // :: error: (assignment.type.incompatible)
    @MungoState({"Next"}) JavaIterator it3 = new JavaIterator();

    while (it3.hasNext()) {
      it3.next();
    }
  }

  public static void assigment3() {
    @MungoState({"HasNext", "Next"}) JavaIterator it = new JavaIterator();

    while (it.hasNext()) {
      it.next();
    }
  }

  public static void assigmentsAndMoves() {
    JavaIterator it = new JavaIterator();

    while (it.hasNext()) {
      JavaIterator alias = it;
      alias.next();
      it = alias;
    }
  }

  public static void assigmentsAndMoves2() {
    JavaIterator it = new JavaIterator();

    while (it.hasNext()) {
      // FIXME The code is safe, but should we error here? Or disallow @MungoState on variable declarations?
      @MungoState({"HasNext", "Next"}) JavaIterator alias = it;
      alias.next();
      it = alias;
    }
  }

  public static void incompatibleArg() {
    JavaIterator it4 = new JavaIterator();
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

  public static JavaIterator didNotComplete3() {
    do {
      // :: error: (Object did not complete its protocol)
      JavaIterator it11 = new JavaIterator();
      if (it11.hasNext()) {
        it11.next();
      }
    } while (true);
  }

  public static void didNotComplete4() {
    while (true) {
      // :: error: (Object did not complete its protocol)
      JavaIterator it12 = new JavaIterator();
      if (it12.hasNext()) {
        it12.next();
      }
    }
  }

  public static JavaIterator returnIsFine() {
    JavaIterator it = new JavaIterator();
    boolean bool = true;
    if (bool) {
      return it;
    }
    return it;
  }

  public static JavaIterator willBeCompleted() {
    JavaIterator it = new JavaIterator();
    return it;
  }

  public static void completeReturned() {
    JavaIterator it = willBeCompleted();
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void completeReturned2() {
    JavaIterator it = new JavaIterator();
    while (it.hasNext()) {
      it.next();
    }
    it = willBeCompleted();
    while (it.hasNext()) {
      it.next();
    }
  }

  public static void leftIncompleteReturned() {
    // :: error: (Returned object did not complete its protocol)
    willBeCompleted();
  }

  public static void leftIncompleteReturned2() {
    // :: error: (Object did not complete its protocol)
    JavaIterator it = willBeCompleted();
    if (it.hasNext()) {
      it.next();
    }
  }

  public static void completeInsideLambda() {
    Supplier<String> fn = () -> {
      JavaIterator it = new JavaIterator();
      while (it.hasNext()) {
        it.next();
      }
      return "";
    };
  }

  public static void completeInsideMethod() {
    Object obj = new Object() {
      public void use() {
        JavaIterator it = new JavaIterator();
        while (it.hasNext()) {
          it.next();
        }
      }
    };
  }

  public static void incompleteInsideLambda() {
    Supplier<String> fn = () -> {
      // :: error: (Object did not complete its protocol)
      JavaIterator it = new JavaIterator();
      if (it.hasNext()) {
        it.next();
      }
      return "";
    };
  }

  public static void incompleteInsideMethod() {
    Object obj = new Object() {
      public void use() {
        // :: error: (Object did not complete its protocol)
        JavaIterator it = new JavaIterator();
        if (it.hasNext()) {
          it.next();
        }
      }
    };
  }

  public static JavaIterator cannotReturnEnded() {
    JavaIterator it13 = new JavaIterator();
    while (it13.hasNext()) {
      it13.next();
    }
    // :: error: (return.type.incompatible)
    return it13;
  }

  public static void use1(JavaIterator it) {
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

  // :: error: (JavaIterator.protocol has no WrongName state)
  // :: error: (State end is final. Will have no effect in @MungoState)
  public static void use3(@MungoState({"Next", "WrongName", "end"}) JavaIterator it) {
    it.next();
    while (it.hasNext()) {
      it.next();
    }
  }

  // :: error: (@MungoState has no meaning since this type has no protocol)
  public static void use4(@MungoState({"state"}) Object it) {

  }

  public static void moveToLambda() {
    // :: error: (Object did not complete its protocol)
    JavaIterator it = new JavaIterator();
    Supplier<String> fn = () -> {
      // :: error: (it was moved to a different closure)
      it.hasNext();
      return "";
    };
  }

  public static void moveToMethod() {
    // :: error: (Object did not complete its protocol)
    JavaIterator it = new JavaIterator();
    Object obj = new Object() {
      public void use() {
        // :: error: (it was moved to a different closure)
        it.hasNext();
      }
    };
  }

}
