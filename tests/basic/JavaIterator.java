import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

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

    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  public static void negatedOk() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    while (!!it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, Next}))
  public static void negatedError() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    while (!it.hasNext()) {
      // :: warning: (it: State{JavaIterator, end})
      // :: error: (Cannot call [next] on State{JavaIterator, end})
      it.next();
    }
  }

  public static void nullUse() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    // :: error: (The previous value of [it] did not complete its protocol (found: State{JavaIterator, HasNext}))
    it = null;

    // :: warning: (it: Null)
    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  public static void nullUse2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext} | Null)
    // :: error: (Cannot call hasNext on null)
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
      // :: warning: (it: State{JavaIterator, HasNext})
      // :: error: (The previous value of [it] did not complete its protocol (found: State{JavaIterator, HasNext}))
      it = null;
    }
  }

  public static void nullOk() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
    // :: warning: (it: State{JavaIterator, end})
    it = null;
  }

  public static void initializedNullOk() {
    JavaIterator it = null;
    // :: warning: (it: Null)
    it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  public static void refineNull(@Nullable JavaIterator it) {
    // :: warning: (it: Shared{JavaIterator} | Null)
    if (it != null) {
      // :: warning: (it: Shared{JavaIterator})
      // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
      while (it.hasNext()) {
        // :: warning: (it: Bottom)
        it.next();
      }
    }
  }

  public static void refineNull2(@Nullable JavaIterator it) {
    // :: warning: (it: Shared{JavaIterator} | Null)
    if (null != it) {
      // :: warning: (it: Shared{JavaIterator})
      // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
      while (it.hasNext()) {
        // :: warning: (it: Bottom)
        it.next();
      }
    }
  }

  public static JavaIterator refineNull3(@Nullable JavaIterator it) {
    // :: warning: (it: Shared{JavaIterator} | Null)
    if (it instanceof JavaIterator) {
      // :: warning: (it: Shared{JavaIterator})
      return it;
    }
    throw new RuntimeException("");
  }

  public static void refineNull4(@Nullable JavaIterator it) {
    // :: warning: (it: Shared{JavaIterator} | Null)
    if (it == null) {
      // :: warning: (it: Null)
      // :: error: (Cannot call hasNext on null)
      it.hasNext();
    } else {
      // :: warning: (it: Shared{JavaIterator})
      // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
      while (it.hasNext()) {
        // :: warning: (it: Bottom)
        it.next();
      }
    }
  }

  public static @Ensures({"HasNext"}) JavaIterator correctReturn(@Requires({"Next"}) JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    it.next();
    // :: warning: (it: State{JavaIterator, HasNext})
    return it;
  }

  public static void override() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    if (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
    // :: warning: (it: State{JavaIterator, HasNext} | State{JavaIterator, end})
    // :: error: (The previous value of [it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
    it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  public static void overrideOk() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
    // :: warning: (it: State{JavaIterator, end})
    it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  public static void whileTrueOk() {
    JavaIterator it = new JavaIterator();

    while (true) {
      // :: warning: (it: State{JavaIterator, HasNext})
      if (it.hasNext()) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      } else {
        break;
      }
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, Next}))
  public static void whileTrueError() {
    JavaIterator it = new JavaIterator();

    while (true) {
      // :: warning: (it: State{JavaIterator, HasNext})
      if (!it.hasNext()) {
        // :: warning: (it: State{JavaIterator, end})
        // :: error: (Cannot call [next] on State{JavaIterator, end})
        it.next();
      } else {
        break;
      }
    }
  }

  public static void assigmentsAndMoves() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      JavaIterator alias = it;
      // :: warning: (alias: State{JavaIterator, Next})
      alias.next();
      // :: warning: (it: Shared{JavaIterator})
      // :: warning: (alias: State{JavaIterator, HasNext})
      it = alias;
    }
  }

  public static void assigmentsAndMoves2() {
    JavaIterator it = new JavaIterator();

    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      JavaIterator alias = it;
      // :: warning: (alias: State{JavaIterator, Next})
      alias.next();
      // :: warning: (it: Shared{JavaIterator})
      // :: warning: (alias: State{JavaIterator, HasNext})
      it = alias;
    }
  }

  // :: error: ([alias] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void assigmentsAndMoves3() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    Object alias = it;
  }

  public static void incompatibleArg() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    // :: error: (Incompatible parameter because State{JavaIterator, HasNext} is not a subtype of State{JavaIterator, Next})
    use2(it);
  }

  public static void validMove() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    if (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      use2(it);
    }
  }

  // :: error: ([moved] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void wrongMove1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    JavaIterator moved = it;
    // :: warning: (it: Shared{JavaIterator})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
    it.hasNext();
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, Next} | State{JavaIterator, end}))
  public static void wrongMove2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    use1(it);
    // :: warning: (it: State{JavaIterator, HasNext})
    it.hasNext();
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
  public static void didNotComplete() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    if (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
  public static void didNotComplete2() {
    if (true) {
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State{JavaIterator, HasNext})
      if (it.hasNext()) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      }
    }
  }

  public static JavaIterator didNotComplete3() {
    do {
      // :: error: (The previous value of [it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State{JavaIterator, HasNext})
      if (it.hasNext()) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      }
    } while (true);
  }

  public static void didNotComplete4() {
    while (true) {
      // :: error: (The previous value of [it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State{JavaIterator, HasNext})
      if (it.hasNext()) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      }
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static JavaIterator didNotComplete5() {
    JavaIterator it = new JavaIterator();
    boolean bool = true;
    if (bool) {
      // :: warning: (it: State{JavaIterator, HasNext})
      return it;
    }
    // :: warning: (it: State{JavaIterator, HasNext})
    return it;
  }

  public static @Ensures("HasNext") JavaIterator willBeCompleted() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    return it;
  }

  public static void completeReturned() {
    JavaIterator it = willBeCompleted();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  public static void completeReturned2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
    // :: warning: (it: State{JavaIterator, end})
    it = willBeCompleted();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  public static void leftIncompleteReturned() {
    // :: error: (Returned value did not complete its protocol (found: State{JavaIterator, HasNext}))
    willBeCompleted();
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
  public static void leftIncompleteReturned2() {
    JavaIterator it = willBeCompleted();
    // :: warning: (it: State{JavaIterator, HasNext})
    if (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  public static void completeInsideLambda() {
    Supplier<String> fn = () -> {
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State{JavaIterator, HasNext})
      while (it.hasNext()) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      }
      return "";
    };
  }

  public static void completeInsideMethod() {
    Object obj = new Object() {
      public void use() {
        JavaIterator it = new JavaIterator();
        // :: warning: (it: State{JavaIterator, HasNext})
        while (it.hasNext()) {
          // :: warning: (it: State{JavaIterator, Next})
          it.next();
        }
      }
    };
  }

  public static void incompleteInsideLambda() {
    // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
    Supplier<String> fn = () -> {
      JavaIterator it = new JavaIterator();
      // :: warning: (it: State{JavaIterator, HasNext})
      if (it.hasNext()) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      }
      return "";
    };
  }

  public static void incompleteInsideMethod() {
    Object obj = new Object() {
      // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
      public void use() {
        JavaIterator it = new JavaIterator();
        // :: warning: (it: State{JavaIterator, HasNext})
        if (it.hasNext()) {
          // :: warning: (it: State{JavaIterator, Next})
          it.next();
        }
      }
    };
  }

  public static JavaIterator returningComplete() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
    // :: warning: (it: State{JavaIterator, end})
    return it;
  }

  public static @Ensures("HasNext") JavaIterator cannotReturnStateEnd() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
    // :: warning: (it: State{JavaIterator, end})
    // :: error: (Incompatible return value because State{JavaIterator, end} is not a subtype of State{JavaIterator, HasNext})
    return it;
  }

  public static @Ensures("HasNext") JavaIterator goodReturn() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    return it;
  }

  public static void use1(JavaIterator it) {
    // :: warning: (it: Shared{JavaIterator})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
    while (it.hasNext()) {
      // :: warning: (it: Bottom)
      it.next();
    }
  }

  public static void use2(@Requires({"Next"}) JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    it.next();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  // :: error: (JavaIterator.protocol has no WrongName state)
  // :: error: (State end is final. Will have no effect in @Requires)
  public static void use3(@Requires({"Next", "WrongName", "end"}) JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    it.next();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

  // :: error: (@Requires has no meaning since this type has no protocol)
  public static void use4(@Requires({"state"}) Object it) {

  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void moveToLambda() {
    JavaIterator it = new JavaIterator();
    Supplier<String> fn = () -> {
      // :: warning: (it: Unknown)
      // :: error: (Cannot access [it])
      it.hasNext();
      return "";
    };
    // :: warning: (fn: NoProtocol{java.util.function.Supplier, exact=true})
    fn.get();
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void moveToLambda2() {
    JavaIterator it = new JavaIterator();
    Supplier<String> fn = () -> {
      // :: warning: (it: Unknown)
      // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
      // :: error: (Cannot access [it])
      System.out.println(it);
      return "";
    };
    // :: warning: (fn: NoProtocol{java.util.function.Supplier, exact=true})
    fn.get();
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void moveToMethod() {
    JavaIterator it = new JavaIterator();
    Object obj = new Object() {
      public void use() {
        // :: warning: (it: Unknown)
        // :: error: (Cannot access [it])
        it.hasNext();
      }
    };
  }

}
