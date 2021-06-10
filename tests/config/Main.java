import java.util.*;

public class Main {

  public static void ok() {
    JavaIteratorImpl it = new JavaIteratorImpl();

    // :: warning: (it: State{JavaIteratorImpl, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIteratorImpl, Next})
      it.next();
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIteratorImpl, Next}))
  public static void notOk() {
    JavaIteratorImpl it = new JavaIteratorImpl();

    // :: warning: (it: State{JavaIteratorImpl, HasNext})
    while (!it.hasNext()) {
      // :: warning: (it: State{JavaIteratorImpl, end})
      // :: error: (Cannot call [next] on State{JavaIteratorImpl, end})
      it.next();
    }
  }

  public static void standardIteratorOk(Object[] args) {
    // :: warning: (args: Shared{java.lang.Object[]})
    Iterator<Object> it = Arrays.asList(args).iterator();

    // :: warning: (it: State{java.util.Iterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{java.util.Iterator, Next})
      it.next();
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{java.util.Iterator, Next}))
  public static void standardIteratorNotOk(Object[] args) {
    // :: warning: (args: Shared{java.lang.Object[]})
    Iterator<Object> it = Arrays.asList(args).iterator();

    // :: warning: (it: State{java.util.Iterator, HasNext})
    while (!it.hasNext()) {
      // :: warning: (it: State{java.util.Iterator, end})
      // :: error: (Cannot call [next] on State{java.util.Iterator, end})
      it.next();
    }
  }

}
