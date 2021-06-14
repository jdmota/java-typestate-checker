import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;

public class Annotations {

  public static void main1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: Shared{JavaIterator} | State{JavaIterator, HasNext})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator} | State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      use1(it);
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public static void use1(@Requires("Next") JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    it.next();
  }

  public static void main2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      use2(it);
    }
  }

  public static void use2(@Requires("Next") @Ensures("HasNext") final JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    it.next();
  }

  public static void main3() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      use2(it);
    }
  }

  // :: error: (Type of parameter [it] is State{JavaIterator, Next}, expected State{JavaIterator, HasNext}})
  public static void use3(@Requires("Next") @Ensures("HasNext") final JavaIterator it) {

  }

  public static void main4() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      use4(it);
    }
  }

  // :: error: (Parameters with @Ensures should be final)
  public static void use4(@Requires("Next") @Ensures("HasNext") JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    if (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    } else {
      // :: warning: (it: State{JavaIterator, end})
      it = new JavaIterator();
    }
  }

  public static void main5() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      use5(it);
    }
  }

  // :: error: (Parameters with @Ensures should be final)
  // :: error: (Type of parameter [it] is State{JavaIterator, HasNext} | State{JavaIterator, end}, expected State{JavaIterator, HasNext}})
  public static void use5(@Requires("Next") @Ensures("HasNext") JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    if (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    } else {
      int i = 3;
      while (i-- > 0) {
        // :: warning: (it: State{JavaIterator, HasNext} | State{JavaIterator, end})
        // :: error: (The previous value of [it] did not complete its protocol (found: State{JavaIterator, HasNext} | State{JavaIterator, end}))
        it = new JavaIterator();
      }
    }
  }

  // :: error: (Type of parameter [it] is State{JavaIterator, HasNext} | State{JavaIterator, end}, expected State{JavaIterator, HasNext}})
  public static void use6(@Requires("Next") @Ensures("HasNext") final JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    if (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    } else {
      int i = 3;
      while (i-- > 0) {
        JavaIterator it2 = new JavaIterator();
        // :: warning: (it2: State{JavaIterator, HasNext})
        while (it2.hasNext()) {
          // :: warning: (it2: State{JavaIterator, Next})
          it2.next();
        }
      }
    }
  }

  public static void use7(@Requires("Next") @Ensures("HasNext") final JavaIterator it) {
    // :: warning: (it: State{JavaIterator, Next})
    it.next();

    int i = 3;
    while (i-- > 0) {
      JavaIterator it2 = new JavaIterator();
      // :: warning: (it2: State{JavaIterator, HasNext})
      while (it2.hasNext()) {
        // :: warning: (it2: State{JavaIterator, Next})
        it2.next();
      }
    }
  }


}
