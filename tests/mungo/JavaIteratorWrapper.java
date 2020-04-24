import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoState;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.function.Supplier;

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper2 {

  private @MungoNullable JavaIterator iterator = null;

  // :: error: (Object did not complete its protocol. Type: JavaIterator{HasNext|Next})
  public void init(JavaIterator it) {

  }

  public boolean hasNext() {
    // :: warning: (iterator: Null)
    // :: error: (Cannot call hasNext on null)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: Bottom)
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper3 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    // :: error: (Cannot call next on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4_2 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended)
    // :: error: (Cannot call hasNext on ended protocol)
    if (iterator.hasNext()) {
      // :: warning: (iterator: JavaIterator{Next})
      return iterator.next();
    }
    return "";
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    while (iterator.hasNext()) {
      // :: warning: (iterator: JavaIterator{Next})
      iterator.next();
    }
    return false;
  }

  public String next() {
    // :: warning: (iterator: Bottom)
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper5 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    use(iterator);
  }

  public boolean hasNext() {
    // :: warning: (iterator: Moved)
    // :: error: (Cannot call hasNext on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: Bottom)
    return iterator.next();
  }

  public static void use(JavaIterator it) {
    // :: warning: (it: JavaIterator{HasNext|Next})
    while (it.hasNext()) {
      // :: warning: (it: JavaIterator{Next})
      it.next();
    }
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper6 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call its own public method)
    hasNext();
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Moved | Null)
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: error: (Cannot call its own public method)
    this.hasNext();
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Moved | Null)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapperWithGetter.protocol")
class JavaIteratorWrapper7 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Moved)
    // :: error: (Cannot call hasNext on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

  public JavaIterator getIterator() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Moved)
    // :: error: (return.type.incompatible)
    return iterator;
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper8 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
    // :: error: (Possible 'this' leak)
    use(this);
  }

  public boolean hasNext() {
    // This error exists because the "use" call invalidates information
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Moved | Null)
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

  // :: error: (Object did not complete its protocol. Type: JavaIteratorWrapper{Start|HasNext|Next})
  public static void use(JavaIteratorWrapper8 it) {

  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper9 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
    // :: error: (Possible 'this' leak)
    JavaIteratorWrapper9 wrapper = this;
    // :: warning: (wrapper: JavaIteratorWrapper{Start|HasNext|Next})
    use(wrapper);
  }

  public boolean hasNext() {
    // This error exists because the "use" call invalidates information
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended | Moved | Null)
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

  // :: error: (Object did not complete its protocol. Type: JavaIteratorWrapper{Start|HasNext|Next})
  public static void use(JavaIteratorWrapper9 it) {

  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper10 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (this was moved to a different closure)
      // :: error: (Possible 'this' leak)
      return this;
    };
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper11 {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (JavaIteratorWrapper11.this was moved to a different closure)
      // :: error: (Possible 'this' leak)
      return JavaIteratorWrapper11.this;
    };
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next})
    return iterator.next();
  }

}

@MungoTypestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapperPropagation {

  private @MungoNullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Null)
    // :: warning: (it: JavaIterator{HasNext|Next})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: JavaIterator{HasNext|Next} | Ended)
    // :: error: (Cannot call hasNext on ended protocol)
    iterator.hasNext();
    return true;
  }

  public String next() {
    // :: warning: (iterator: JavaIterator{Next} | Ended)
    // :: error: (Cannot call next on ended protocol)
    return iterator.next();
  }

}
