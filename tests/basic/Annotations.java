import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Ensures;

public class Annotations {

  public static void main1() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext" | Moved)
    // :: error: (Cannot call hasNext on moved value)
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      use1(it);
    }
  }

  // :: error: (Object did not complete its protocol. Type: State "HasNext")
  public static void use1(@Requires("Next") JavaIterator it) {
    // :: warning: (it: State "Next")
    it.next();
  }

  public static void main2() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      use2(it);
    }
  }

  public static void use2(@Requires("Next") @Ensures("HasNext") JavaIterator it) {
    // :: warning: (it: State "Next")
    it.next();
  }

  public static void main3() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      use2(it);
    }
  }

  // :: error: (Final type does not match what was specified by @Ensures. Type: State "Next")
  public static void use3(@Requires("Next") @Ensures("HasNext") JavaIterator it) {

  }

  public static void main4() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      use4(it);
    }
  }

  public static void use4(@Requires("Next") @Ensures("HasNext") JavaIterator it) {
    // :: warning: (it: State "Next")
    if (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    } else {
      // :: warning: (it: Ended)
      // :: error: (Cannot override because object is not in the state specified by @Ensures. Type: Ended)
      it = new JavaIterator();
    }
  }

  public static void main5() {
    JavaIterator it = new JavaIterator();
    // :: warning: (it: State "HasNext")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      use5(it);
    }
  }

  // :: error: (Final type does not match what was specified by @Ensures. Type: State "HasNext" | Ended)
  public static void use5(@Requires("Next") @Ensures("HasNext") JavaIterator it) {
    // :: warning: (it: State "Next")
    if (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    } else {
      int i = 3;
      while (i-- > 0) {
        // :: warning: (it: State "HasNext" | Ended)
        // :: error: (Cannot override because object has not ended its protocol. Type: State "HasNext" | Ended)
        // :: error: (Cannot override because object is not in the state specified by @Ensures. Type: State "HasNext" | Ended)
        it = new JavaIterator();
      }
    }
  }

}
