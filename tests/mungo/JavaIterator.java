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

    it = null;

    while (it.hasNext()) {
      it.next();
    }
  }

  public static void use(JavaIterator it2) {
    while (it2.hasNext()) {
      it2.next();
    }
  }

}
