import org.checkerframework.checker.mungo.lib.MungoTypestate;

import java.util.Iterator;

@MungoTypestate("JavaIterator.protocol")
class JavaIterator implements Iterator<Object> {

  @Override
  public boolean hasNext() {
    return false;
  }

  @Override
  public Object next() {
    return null;
  }

  public static void main(String[] args) {
    JavaIterator it = new JavaIterator();

    while (it.hasNext()) {
      it.next();
    }
  }

  public static void main2(String[] args) {
    JavaIterator it = new JavaIterator();
    it = null;

    // :: error: (Cannot call hasNext because it is null)
    while (it.hasNext()) {
      // :: error: (Cannot call next because it has the bottom type)
      it.next();
    }
  }

  public static void main3(String[] args) {
    JavaIterator it = new JavaIterator();

    // :: error: (Cannot call hasNext. (Unknown states))
    while (it.hasNext()) {
      // :: error: (Cannot call next. (Unknown states))
      it.next();
      it = null;
    }
  }

  public static void main4(String[] args) {
    JavaIterator it = new JavaIterator();

    while (true) {
      if (it.hasNext()) {
        it.next();
      } else {
        break;
      }
    }
  }

  public static void main5(String[] args) {
    JavaIterator it = new JavaIterator();

    while (true) {
      if (!it.hasNext()) {
        // :: error: (Cannot call next on states end. (Inferred: end))
        it.next();
      } else {
        break;
      }
    }
  }

  public static void use(JavaIterator it2) {
    // :: error: (Cannot call hasNext on states end, Next. (Inferred: end, HasNext, Next))
    while (it2.hasNext()) {
      it2.next();
    }
  }

}
