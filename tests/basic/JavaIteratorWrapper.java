import org.checkerframework.checker.jtc.lib.Typestate;
import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper2 {

  private @Nullable JavaIterator iterator = null;

  // :: error: (Object did not complete its protocol. Type: State "HasNext" | State "Next")
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

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper3 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    // :: error: (Cannot call next on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4_2 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended)
    // :: error: (Cannot call hasNext on ended protocol)
    if (iterator.hasNext()) {
      // :: warning: (iterator: State "Next")
      return iterator.next();
    }
    return "";
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    while (iterator.hasNext()) {
      // :: warning: (iterator: State "Next")
      iterator.next();
    }
    return false;
  }

  public String next() {
    // :: warning: (iterator: Bottom)
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper5 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
    // :: warning: (iterator: State "HasNext" | State "Next")
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
    // :: warning: (it: State "HasNext" | State "Next")
    while (it.hasNext()) {
      // :: warning: (it: State "Next")
      it.next();
    }
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper6 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call its own public method)
    hasNext();
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended | Null | Moved)
    // :: error: (Cannot call hasNext on null, on ended protocol, on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: error: (Cannot call its own public method)
    this.hasNext();
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended | Null | Moved)
    // :: error: (Cannot call next on null, on ended protocol, on moved value, on state HasNext (got: HasNext, Next))
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapperWithGetter.protocol")
class JavaIteratorWrapper7 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Moved)
    // :: error: (Cannot call hasNext on moved value)
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

  public JavaIterator getIterator() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Moved)
    // :: error: (return.type.incompatible)
    return iterator;
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper8 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
    // :: error: (Possible 'this' leak)
    use(this);
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

  // :: error: (Object did not complete its protocol. Type: State "Start" | State "HasNext" | State "Next")
  public static void use(JavaIteratorWrapper8 it) {

  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper9 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
    // :: error: (Possible 'this' leak)
    JavaIteratorWrapper9 wrapper = this;
    // :: warning: (wrapper: State "Start" | State "HasNext" | State "Next" | Ended | Moved)
    // :: error: (argument.type.incompatible)
    use(wrapper);
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

  // :: error: (Object did not complete its protocol. Type: State "Start" | State "HasNext" | State "Next")
  public static void use(JavaIteratorWrapper9 it) {

  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper10 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (this was moved to a different closure)
      // :: error: (Possible 'this' leak)
      return this;
    };
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper11 {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (JavaIteratorWrapper11.this was moved to a different closure)
      // :: error: (Possible 'this' leak)
      return JavaIteratorWrapper11.this;
    };
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next")
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (iterator: State "Next")
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapperPropagation {

  private @Nullable JavaIterator iterator = null;

  public void init(JavaIterator it) {
    // :: warning: (iterator: Null)
    // :: warning: (it: State "HasNext" | State "Next")
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (iterator: State "HasNext" | State "Next" | Ended)
    // :: error: (Cannot call hasNext on ended protocol)
    iterator.hasNext();
    return true;
  }

  public String next() {
    // :: warning: (iterator: State "Next" | Ended)
    // :: error: (Cannot call next on ended protocol)
    return iterator.next();
  }

}
