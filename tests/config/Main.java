import java.util.*;

public class Main {

  public static void ok() {
    JavaIteratorImpl it = new JavaIteratorImpl();

    // :: warning: (it: JavaIterator{HasNext})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      // :: error: (Returned object did not complete its protocol. Type: Object | Moved)
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
      // :: error: (Returned object did not complete its protocol. Type: Object | Moved)
      it.next();
    }
  }

  // TODO improve this: know that iterator() returns a new iterator in the initial state
  // TODO improve this: generics
  // TODO why the assignment.type.incompatible error?

  public static void standardIteratorOk(Object[] args) {
    // :: error: (assignment.type.incompatible)
    Iterator<Object> it = Arrays.asList(args).iterator();

    // :: warning: (it: JavaIterator{HasNext|Next} | Ended | Moved)
    // :: error: (Cannot call hasNext on ended protocol, on moved value)
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      // :: error: (Returned object did not complete its protocol. Type: Object | Moved)
      it.next();
    }
  }

  public static void standardIteratorNotOk(Object[] args) {
    // :: error: (assignment.type.incompatible)
    // :: error: (Object did not complete its protocol. Type: JavaIterator{Next})
    Iterator<Object> it = Arrays.asList(args).iterator();

    // :: warning: (it: JavaIterator{HasNext|Next} | Ended | Moved)
    // :: error: (Cannot call hasNext on ended protocol, on moved value)
    while (!it.hasNext()) {
      // :: warning: (it: Ended)
      // :: error: (Cannot call next on ended protocol)
      // :: error: (Returned object did not complete its protocol. Type: Object | Moved)
      it.next();
    }
  }

}
