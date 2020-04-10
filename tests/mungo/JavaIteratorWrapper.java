import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper2 {

  private @MungoNullable JavaIterator iterator = null;

  // :: error: (Object did not complete its protocol)
  public void init(JavaIterator it) {

  }

  public boolean hasNext() {
    // :: error: (Cannot call hasNext on null)
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper3 {

  // :: error: (Object did not complete its protocol)
  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: error: (Cannot call next on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4_2 {

  // :: error: (Object did not complete its protocol)
  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: error: (Cannot call hasNext on ended protocol)
    if (iterator.hasNext()) {
      return iterator.next();
    }
    return "";
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call hasNext on ended protocol)
    while (iterator.hasNext()) {
      iterator.next();
    }
    return false; // TODO detect that this always returns false and "next" will never be called?
  }

  public String next() {
    // :: error: (Cannot call next on ended protocol)
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper5 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
    use(iterator);
  }

  public boolean hasNext() {
    // :: error: (Cannot call hasNext on moved value)
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

  public static void use(JavaIterator it) {
    while (it.hasNext()) {
      it.next();
    }
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper6 {

  // :: error: (Object did not complete its protocol)
  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call its own public method)
    hasNext();
    // :: error: (Cannot call hasNext on unknown)
    return iterator.hasNext();
  }

  public String next() {
    // :: error: (Cannot call its own public method)
    this.hasNext();
    // :: error: (Cannot call next on unknown)
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapperWithGetter.protocol")
class JavaIteratorWrapper7 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call hasNext on moved value)
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

  public JavaIterator getIterator() {
    // TODO better message, the problem is that calling getIterator() once moves it
    // :: error: (return.type.incompatible)
    return iterator;
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper8 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
    // :: error: (Possible 'this' leak)
    use(this);
  }

  public boolean hasNext() {
    // This error exists because the "use" call invalidates information
    // :: error: (Cannot call hasNext on null)
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

  // :: error: (Object did not complete its protocol)
  public static void use(JavaIteratorWrapper8 it) {

  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper9 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
    // :: error: (Possible 'this' leak)
    JavaIteratorWrapper9 wrapper = this;
    use(wrapper);
  }

  public boolean hasNext() {
    // This error exists because the "use" call invalidates information
    // :: error: (Cannot call hasNext on null)
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

  // :: error: (Object did not complete its protocol)
  public static void use(JavaIteratorWrapper9 it) {

  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper10 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (this was moved to a different closure)
      // :: error: (Possible 'this' leak)
      return this;
    };
  }

  public boolean hasNext() {
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper11 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (JavaIteratorWrapper11.this was moved to a different closure)
      // :: error: (Possible 'this' leak)
      return JavaIteratorWrapper11.this;
    };
  }

  public boolean hasNext() {
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

}
