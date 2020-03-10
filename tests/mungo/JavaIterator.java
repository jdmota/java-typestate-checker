import org.checkerframework.checker.mungo.qual.MungoTypestate;

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

}
