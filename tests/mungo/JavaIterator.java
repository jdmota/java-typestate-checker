import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoRequires;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

@MungoTypestate("JavaIterator.protocol")
public class JavaIterator {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  public static void basicOk() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void negatedOk() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: JavaIterator{HasNext})
    while (!!it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void negatedError() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{Next})
    JavaIterator it = new JavaIterator();

    // :: warning: (it: JavaIterator{HasNext})
    while (!it.hasNext()) {
      // :: warning: (it: Ended)
      // :: error: (Cannot call next on ended protocol)
      it.next();
    }
  }

  public static void nullUse() {
    @MungoNullable JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext|Next} | Null)
    // :: error: (Cannot override because object has not ended its protocol. Type: JavaIterator{HasNext})
    it = null;

    // :: warning: (it: Null)
    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  public static void nullUse2() {
    @MungoNullable JavaIterator it = new JavaIterator();

    // :: warning: (it: JavaIterator{HasNext} | Null)
    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
      // :: warning: (it: JavaIterator{HasNext|Next} | Null)
      // :: error: (Cannot override because object has not ended its protocol. Type: JavaIterator{HasNext})
      it = null;
    }
  }

  public static void nullOk() {
    @MungoNullable JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
    // :: warning: (it: JavaIterator{HasNext|Next} | Null)
    it = null;
  }

  public static void initializedNull() {
    // :: error: (assignment.type.incompatible)
    JavaIterator it = null;
    // :: warning: (it: JavaIterator{HasNext|Next})
    it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void initializedNullOk() {
    @MungoNullable JavaIterator it = null;
    // :: warning: (it: JavaIterator{HasNext|Next} | Null)
    it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void refineNull(@MungoNullable JavaIterator it) {
    // :: warning: (it: JavaIterator{HasNext|Next} | Null)
    if (it != null) {
      // :: warning: (it: JavaIterator{HasNext|Next})
      while (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
    }
  }

  public static void refineNull2(@MungoNullable JavaIterator it) {
    // :: warning: (it: JavaIterator{HasNext|Next} | Null)
    if (null != it) {
      // :: warning: (it: JavaIterator{HasNext|Next})
      while (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
    }
  }

  public static JavaIterator refineNull3(@MungoNullable JavaIterator it) {
    // :: warning: (it: JavaIterator{HasNext|Next} | Null)
    if (it instanceof JavaIterator) {
      // :: warning: (it: JavaIterator{HasNext|Next})
      return it;
    }
    throw new RuntimeException("");
  }

  public static void refineNull4(@MungoNullable JavaIterator it) {
    // :: warning: (it: JavaIterator{HasNext|Next} | Null)
    if (it == null) {
      // :: warning: (it: Null)
      // :: error: (Cannot call hasNext on null)
      it.hasNext();
    } else {
      // :: warning: (it: JavaIterator{HasNext|Next})
      while (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
    }
  }

  public static @MungoState({"HasNext"}) JavaIterator correctReturn(@MungoRequires({"Next"}) JavaIterator it) {
    // :: warning: (it: JavaIterator{Next})
    it.next();
    // :: warning: (it: JavaIterator{HasNext})
    return it;
  }

  public static void override() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    if (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
    // :: warning: (it: JavaIterator{HasNext|Next})
    // :: error: (Cannot override because object has not ended its protocol. Type: JavaIterator{HasNext} | Ended)
    it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void overrideOk() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
    // :: warning: (it: JavaIterator{HasNext|Next})
    it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void whileTrueOk() {
    JavaIterator it = new JavaIterator();

    while (true) {
      // :: warning: (it: JavaIterator{HasNext})
      if (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      } else {
        break;
      }
    }
  }

  public static void whileTrueError() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{Next})
    JavaIterator it = new JavaIterator();

    while (true) {
      // :: warning: (it: JavaIterator{HasNext})
      if (!it.hasNext()) {
        // :: warning: (it: Ended)
        // :: error: (Cannot call next on ended protocol)
        it.next();
      } else {
        break;
      }
    }
  }

  public static void assigmentsAndMoves() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      JavaIterator alias = it;
      // :: warning: (alias: JavaIterator{Next})
      alias.next();
      // :: warning: (it: JavaIterator{HasNext|Next})
      // :: warning: (alias: JavaIterator{HasNext})
      it = alias;
    }
  }

  public static void assigmentsAndMoves2() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      JavaIterator alias = it;
      // :: warning: (alias: JavaIterator{Next})
      alias.next();
      // :: warning: (it: JavaIterator{HasNext|Next})
      // :: warning: (alias: JavaIterator{HasNext})
      it = alias;
    }
  }

  public static void assigmentsAndMoves3() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext})
    Object alias = it;
  }

  public static void incompatibleArg() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    // :: error: (argument.type.incompatible)
    use2(it);
  }

  public static void validMove() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    if (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      use2(it);
    }
  }

  public static void wrongMove1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext})
    JavaIterator moved = it;
    // :: warning: (it: Moved)
    // :: error: (Cannot call hasNext on moved value)
    it.hasNext();
  }

  public static void wrongMove2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    use1(it);
    // :: warning: (it: Moved)
    // :: error: (Cannot call hasNext on moved value)
    it.hasNext();
  }

  public static void didNotComplete() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext} | Ended)
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    if (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void didNotComplete2() {
    if (true) {
      // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext} | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: JavaIterator{HasNext})
      if (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
    }
  }

  public static JavaIterator didNotComplete3() {
    do {
      // :: error: (Object has not ended its protocol. Type: JavaIterator{HasNext} | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: JavaIterator{HasNext})
      if (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
    } while (true);
  }

  public static void didNotComplete4() {
    while (true) {
      // :: error: (Object has not ended its protocol. Type: JavaIterator{HasNext} | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: JavaIterator{HasNext})
      if (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
    }
  }

  public static JavaIterator returnIsFine() {
    JavaIterator it = new JavaIterator();
    boolean bool = true;
    if (bool) {
      // :: warning: (it: JavaIterator{HasNext})
      return it;
    }
    // :: warning: (it: JavaIterator{HasNext})
    return it;
  }

  public static JavaIterator willBeCompleted() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    return it;
  }

  public static void completeReturned() {
    JavaIterator it = willBeCompleted();
    // :: warning: (it: JavaIterator{HasNext|Next})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void completeReturned2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
    // :: warning: (it: JavaIterator{HasNext|Next})
    it = willBeCompleted();
    // :: warning: (it: JavaIterator{HasNext|Next})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void leftIncompleteReturned() {
    // :: error: (Returned object did not complete its protocol. Type: JavaIterator{HasNext|Next})
    willBeCompleted();
  }

  public static void leftIncompleteReturned2() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext} | Ended)
    JavaIterator it = willBeCompleted();
    // :: warning: (it: JavaIterator{HasNext|Next})
    if (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void completeInsideLambda() {
    Supplier<String> fn = () -> {
      JavaIterator it = new JavaIterator();
      // :: warning: (it: JavaIterator{HasNext})
      while (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
      return "";
    };
  }

  public static void completeInsideMethod() {
    Object obj = new Object() {
      public void use() {
        JavaIterator it = new JavaIterator();
        // :: warning: (it: JavaIterator{HasNext})
        while (it.hasNext()) {
          // :: warning: (it: JavaIterator{Next})
          it.next();
        }
      }
    };
  }

  public static void incompleteInsideLambda() {
    Supplier<String> fn = () -> {
      // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext} | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: JavaIterator{HasNext})
      if (it.hasNext()) {
        // :: warning: (it: JavaIterator{Next})
        it.next();
      }
      return "";
    };
  }

  public static void incompleteInsideMethod() {
    Object obj = new Object() {
      public void use() {
        // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext} | Ended)
        JavaIterator it = new JavaIterator();
        // :: warning: (it: JavaIterator{HasNext})
        if (it.hasNext()) {
          // :: warning: (it: JavaIterator{Next})
          it.next();
        }
      }
    };
  }

  public static JavaIterator cannotReturnEnded() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
    // :: warning: (it: Ended)
    // :: error: (return.type.incompatible)
    return it;
  }

  public static void use1(JavaIterator it) {
    // :: warning: (it: JavaIterator{HasNext|Next})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  public static void use2(@MungoRequires({"Next"}) JavaIterator it) {
    // :: warning: (it: JavaIterator{Next})
    it.next();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  // :: error: (JavaIterator.protocol has no WrongName state)
  // :: error: (State end is final. Will have no effect in @MungoRequires)
  public static void use3(@MungoRequires({"Next", "WrongName", "end"}) JavaIterator it) {
    // :: warning: (it: JavaIterator{Next})
    it.next();
    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

  // :: error: (@MungoRequires has no meaning in Object type)
  // :: error: (Object did not complete its protocol. Type: Object)
  public static void use4(@MungoRequires({"state"}) Object it) {

  }

  public static void moveToLambda() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext})
    JavaIterator it = new JavaIterator();
    Supplier<String> fn = () -> {
      // :: warning: (it: Bottom)
      // :: error: (it was moved to a different closure)
      it.hasNext();
      return "";
    };
  }

  public static void moveToLambda2() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext})
    JavaIterator it = new JavaIterator();
    Supplier<String> fn = () -> {
      // :: warning: (it: Bottom)
      // :: error: (it was moved to a different closure)
      System.out.println(it);
      return "";
    };
  }

  public static void moveToMethod() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext})
    JavaIterator it = new JavaIterator();
    Object obj = new Object() {
      public void use() {
        // :: warning: (it: Bottom)
        // :: error: (it was moved to a different closure)
        it.hasNext();
      }
    };
  }

}
