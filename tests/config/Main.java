import java.util.*;

public class Main {

  public static void ok() {
    JavaIteratorImpl it = new JavaIteratorImpl();

    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      // :: error: (Returned object did not complete its protocol. Type: Object)
      it.next();
    }
  }

  public static void notOk() {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{Next})
    JavaIteratorImpl it = new JavaIteratorImpl();

    // :: warning: (it: JavaIterator{HasNext})
    while (!it.hasNext()) {
      // :: warning: (it: Ended)
      // :: error: (Cannot call next on ended protocol)
      // :: error: (Returned object did not complete its protocol. Type: Object)
      it.next();
    }
  }

  public static void standardIteratorOk(Object[] args) {
    Iterator<Object> it = Arrays.asList(args).iterator();

    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      // :: error: (Returned object did not complete its protocol. Type: Object | Moved)
      it.next();
    }
  }

  public static void standardIteratorNotOk(Object[] args) {
    // :: error: (Object did not complete its protocol. Type: JavaIterator{Next})
    Iterator<Object> it = Arrays.asList(args).iterator();

    // :: warning: (it: JavaIterator{HasNext})
    while (!it.hasNext()) {
      // :: warning: (it: Ended)
      // :: error: (Cannot call next on ended protocol)
      // :: error: (Returned object did not complete its protocol. Type: Object | Moved)
      it.next();
    }
  }

}
