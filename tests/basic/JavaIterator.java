import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.State;
import org.checkerframework.checker.jtc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIterator.protocol")
public class JavaIterator {

  public boolean hasNext() {
    return false;
  }

  public String next() {
    return "";
  }

  public static void basicOk() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void negatedOk() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    while (!!it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void negatedError() {
    // :: error: (Object did not complete its protocol. Type: State "Next")
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    while (!it.hasNext()) {
      // :: warning: (it: Ended)
      // :: error: (Cannot call next on ended protocol)
      it.next();
    }
  }

  public static void nullUse() {
    @Nullable JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    // :: error: (Cannot override because object has not ended its protocol. Type: State "HasNext")
    it = null;

    // :: warning: (it: Null)
    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  public static void nullUse2() {
    @Nullable JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext" | Null)
    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
      // :: warning: (it: State "HasNext")
      // :: error: (Cannot override because object has not ended its protocol. Type: State "HasNext")
      it = null;
    }
  }

  public static void nullOk() {
    @Nullable JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
    // :: warning: (it: Ended)
    it = null;
  }

  public static void initializedNull() {
    // :: error: (assignment.type.incompatible)
    JavaIterator it = null;
    // :: warning: (it: Null)
    it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void initializedNullOk() {
    @Nullable JavaIterator it = null;
    // :: warning: (it: Null)
    it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void refineNull(@Nullable JavaIterator it) {
    // :: warning: (it: State "HasNext" | State "Next" | Null)
    if (it != null) {
      // :: warning: (it: State "HasNext" | State "Next")
      while (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
    }
  }

  public static void refineNull2(@Nullable JavaIterator it) {
    // :: warning: (it: State "HasNext" | State "Next" | Null)
    if (null != it) {
      // :: warning: (it: State "HasNext" | State "Next")
      while (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
    }
  }

  public static JavaIterator refineNull3(@Nullable JavaIterator it) {
    // :: warning: (it: State "HasNext" | State "Next" | Null)
    if (it instanceof JavaIterator) {
      // :: warning: (it: State "HasNext" | State "Next")
      return it;
    }
    throw new RuntimeException("");
  }

  public static void refineNull4(@Nullable JavaIterator it) {
    // :: warning: (it: State "HasNext" | State "Next" | Null)
    if (it == null) {
      // :: warning: (it: Null)
      // :: error: (Cannot call hasNext on null)
      it.hasNext();
    } else {
      // :: warning: (it: State "HasNext" | State "Next")
      while (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
    }
  }

  public static @State({"HasNext"}) JavaIterator correctReturn(@Requires({"Next"}) JavaIterator it) {
    // :: warning: (it: State "Next")
    it.next();
    // :: warning: (it: State "HasNext")
    return it;
  }

  public static void override() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    if (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
    // :: warning: (it: State "HasNext" | Ended)
    // :: error: (Cannot override because object has not ended its protocol. Type: State "HasNext" | Ended)
    it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void overrideOk() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
    // :: warning: (it: Ended)
    it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void whileTrueOk() {
    JavaIterator it = new JavaIterator();

    while (true) {
      // :: warning: (it: State "HasNext")
      if (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      } else {
        break;
      }
    }
  }

  public static void whileTrueError() {
    // :: error: (Object did not complete its protocol. Type: State "Next")
    JavaIterator it = new JavaIterator();

    while (true) {
      // :: warning: (it: State "HasNext")
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

    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      JavaIterator alias = it;
      // :: warning: (alias: State "Next")
      alias.next();
      // :: warning: (it: Moved)
      // :: warning: (alias: State "HasNext")
      it = alias;
    }
  }

  public static void assigmentsAndMoves2() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      JavaIterator alias = it;
      // :: warning: (alias: State "Next")
      alias.next();
      // :: warning: (it: Moved)
      // :: warning: (alias: State "HasNext")
      it = alias;
    }
  }

  public static void assigmentsAndMoves3() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    // :: error: (Up-casting not allowed. Left-hand-side has no protocol.)
    Object alias = it;
  }

  public static void incompatibleArg() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    // :: error: (argument.type.incompatible)
    use2(it);
  }

  public static void validMove() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    if (it.hasNext()) {
      // :: warning: (it: State "Next")
      use2(it);
    }
  }

  public static void wrongMove1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    JavaIterator moved = it;
    // :: warning: (it: Moved)
    // :: error: (Cannot call hasNext on moved value)
    it.hasNext();
  }

  public static void wrongMove2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    use1(it);
    // :: warning: (it: Moved)
    // :: error: (Cannot call hasNext on moved value)
    it.hasNext();
  }

  public static void didNotComplete() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext" | Ended)
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    if (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void didNotComplete2() {
    if (true) {
      // :: error: (Object did not complete its protocol. Type: State "HasNext" | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State "HasNext")
      if (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
    }
  }

  public static JavaIterator didNotComplete3() {
    do {
      // :: error: (Object has not ended its protocol. Type: State "HasNext" | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State "HasNext")
      if (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
    } while (true);
  }

  public static void didNotComplete4() {
    while (true) {
      // :: error: (Object has not ended its protocol. Type: State "HasNext" | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State "HasNext")
      if (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
    }
  }

  public static JavaIterator returnIsFine() {
    JavaIterator it = new JavaIterator();
    boolean bool = true;
    if (bool) {
      // :: warning: (it: State "HasNext")
      return it;
    }
    // :: warning: (it: State "HasNext")
    return it;
  }

  public static JavaIterator willBeCompleted() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    return it;
  }

  public static void completeReturned() {
    JavaIterator it = willBeCompleted();
    // :: warning: (it: State "HasNext" | State "Next")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void completeReturned2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
    // :: warning: (it: Ended)
    it = willBeCompleted();
    // :: warning: (it: State "HasNext" | State "Next")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void leftIncompleteReturned() {
    // :: error: (Returned object did not complete its protocol. Type: State "HasNext" | State "Next")
    willBeCompleted();
  }

  public static void leftIncompleteReturned2() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext" | Ended)
    JavaIterator it = willBeCompleted();
    // :: warning: (it: State "HasNext" | State "Next")
    if (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void completeInsideLambda() {
    Supplier<String> fn = () -> {
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State "HasNext")
      while (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
      return "";
    };
  }

  public static void completeInsideMethod() {
    Object obj = new Object() {
      public void use() {
        JavaIterator it = new JavaIterator();
        // :: warning: (it: State "HasNext")
        while (it.hasNext()) {
          // :: warning: (it: State "Next")
          it.next();
        }
      }
    };
  }

  public static void incompleteInsideLambda() {
    Supplier<String> fn = () -> {
      // :: error: (Object did not complete its protocol. Type: State "HasNext" | Ended)
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State "HasNext")
      if (it.hasNext()) {
        // :: warning: (it: State "Next")
        it.next();
      }
      return "";
    };
  }

  public static void incompleteInsideMethod() {
    Object obj = new Object() {
      public void use() {
        // :: error: (Object did not complete its protocol. Type: State "HasNext" | Ended)
        JavaIterator it = new JavaIterator();
        // :: warning: (it: State "HasNext")
        if (it.hasNext()) {
          // :: warning: (it: State "Next")
          it.next();
        }
      }
    };
  }

  public static JavaIterator cannotReturnEnded() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
    // :: warning: (it: Ended)
    // :: error: (return.type.incompatible)
    return it;
  }

  public static void use1(JavaIterator it) {
    // :: warning: (it: State "HasNext" | State "Next")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  public static void use2(@Requires({"Next"}) JavaIterator it) {
    // :: warning: (it: State "Next")
    it.next();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  // :: error: (JavaIterator.protocol has no WrongName state)
  // :: error: (State end is final. Will have no effect in @Requires)
  public static void use3(@Requires({"Next", "WrongName", "end"}) JavaIterator it) {
    // :: warning: (it: State "Next")
    it.next();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

  // :: error: (@Requires has no meaning in Object type)
  // :: error: (Object did not complete its protocol. Type: Object)
  public static void use4(@Requires({"state"}) Object it) {

  }

  public static void moveToLambda() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    JavaIterator it = new JavaIterator();
    Supplier<String> fn = () -> {
      // :: warning: (it: Bottom)
      // :: error: (it was moved to a different closure)
      it.hasNext();
      return "";
    };
  }

  public static void moveToLambda2() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
    JavaIterator it = new JavaIterator();
    Supplier<String> fn = () -> {
      // :: warning: (it: Bottom)
      // :: error: (it was moved to a different closure)
      // :: error: (Up-casting not allowed. Left-hand-side has no protocol.)
      System.out.println(it);
      return "";
    };
  }

  public static void moveToMethod() {
    // :: error: (Object did not complete its protocol. Type: State "HasNext")
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
