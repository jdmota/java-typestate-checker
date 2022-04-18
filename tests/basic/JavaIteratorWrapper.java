import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.function.Supplier;

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper1 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper2 {

  private @Nullable JavaIterator iterator = null;

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, HasNext}))
  public void init(@Requires("HasNext") JavaIterator it) {

  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Null)
    // :: error: (Cannot call hasNext on null)
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper3 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: error: (Cannot call [next] on State{JavaIterator, HasNext})
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4_2 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    return true;
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext} | State{JavaIterator, end})
    // :: error: (Cannot call [hasNext] on State{JavaIterator, HasNext} | State{JavaIterator, end})
    if (iterator.hasNext()) {
      // :: warning: (this.iterator: State{JavaIterator, Next})
      return iterator.next();
    }
    return "";
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper4 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    while (iterator.hasNext()) {
      // :: warning: (this.iterator: State{JavaIterator, Next})
      iterator.next();
    }
    return false;
  }

  public String next() {
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper5 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    use(iterator);
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Shared{JavaIterator})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator})
    return iterator.hasNext();
  }

  public String next() {
    return iterator.next();
  }

  public static void use(@Requires("HasNext") JavaIterator it) {
    // :: warning: (it: State{JavaIterator, HasNext})
    while (it.hasNext()) {
      // :: warning: (it: State{JavaIterator, Next})
      it.next();
    }
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper6 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: error: (Cannot call own public method [hasNext])
    hasNext();
    // :: warning: (this.iterator: Bottom)
    return iterator.hasNext();
  }

  public String next() {
    this.hasNext();
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapperWithGetter.protocol")
class JavaIteratorWrapper7 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, HasNext})
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, Next})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator} | State{JavaIterator, HasNext})
    // :: error: (Cannot call [hasNext] on Shared{JavaIterator} | State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, Next})
    // :: error: (Cannot call [next] on Shared{JavaIterator} | State{JavaIterator, Next})
    return iterator.next();
  }

  public @Ensures({"HasNext", "Next"}) JavaIterator getIterator() {
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, HasNext})
    // :: warning: (this.iterator: Shared{JavaIterator} | State{JavaIterator, Next})
    // :: error: (Incompatible return value: cannot cast from Shared{JavaIterator} | State{JavaIterator, HasNext} to State{JavaIterator, HasNext})
    // :: error: (Incompatible return value: cannot cast from Shared{JavaIterator} | State{JavaIterator, Next} to State{JavaIterator, HasNext})
    return iterator;
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper8 {

  private @Nullable JavaIterator iterator = null;

  // :: error: (Type of parameter [this] is Shared{JavaIteratorWrapper8}, expected State{JavaIteratorWrapper8, ?}})
  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    // :: error: (Incompatible parameter: cannot cast from State{JavaIteratorWrapper8, ?} to State{JavaIteratorWrapper8, HasNext})
    use(this);
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.next();
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIteratorWrapper8, HasNext}))
  public static void use(@Requires("HasNext") JavaIteratorWrapper8 it) {

  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper9 {

  private @Nullable JavaIterator iterator = null;

  // :: error: (Type of parameter [this] is Shared{JavaIteratorWrapper9}, expected State{JavaIteratorWrapper9, ?}})
  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    JavaIteratorWrapper9 wrapper = this;
    // :: warning: (wrapper: State{JavaIteratorWrapper9, ?})
    // :: error: (Incompatible parameter: cannot cast from State{JavaIteratorWrapper9, ?} to Shared{JavaIteratorWrapper9})
    use(wrapper);
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.next();
  }

  public static void use(JavaIteratorWrapper9 it) {

  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper10 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (Cannot access [this])
      return this;
    };
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapper11 {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
    Supplier<Object> fn = () -> {
      // :: error: (Cannot access [this])
      return JavaIteratorWrapper11.this;
    };
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.hasNext();
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next})
    return iterator.next();
  }

}

@Typestate("JavaIteratorWrapper.protocol")
class JavaIteratorWrapperPropagation {

  private @Nullable JavaIterator iterator = null;

  public void init(@Requires("HasNext") JavaIterator it) {
    // :: warning: (this.iterator: Null)
    // :: warning: (it: State{JavaIterator, HasNext})
    iterator = it;
  }

  public boolean hasNext() {
    // :: warning: (this.iterator: State{JavaIterator, HasNext})
    // :: warning: (this.iterator: State{JavaIterator, Next} | State{JavaIterator, end})
    // :: error: (Cannot call [hasNext] on State{JavaIterator, Next} | State{JavaIterator, end})
    iterator.hasNext();
    return true;
  }

  public String next() {
    // :: warning: (this.iterator: State{JavaIterator, Next} | State{JavaIterator, end})
    // :: error: (Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end})
    return iterator.next();
  }

}
