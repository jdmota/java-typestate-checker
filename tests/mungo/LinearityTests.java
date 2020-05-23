import org.checkerframework.checker.mungo.lib.MungoTypestate;
import org.checkerframework.checker.mungo.lib.MungoRequires;
import org.checkerframework.checker.mungo.lib.MungoEnsures;
import org.checkerframework.checker.mungo.lib.MungoNullable;

import java.util.*;
import java.util.function.*;

@MungoTypestate("Linearity.protocol")
class Linearity {

  public void a() {
  }

  public void b() {
  }

  public void finish() {
  }

  public void useOther(@MungoRequires("State0") Linearity obj) {
    // :: warning: (obj: Linearity{State0})
    obj.a();
    // :: warning: (obj: Linearity{State1})
    obj.b();
  }

  private void moveThis1() {
    // :: error: (Possible 'this' leak)
    LinearityTests.use(this);
  }

  private void moveThis2() {
    // :: error: (Possible 'this' leak)
    LinearityTests.use(Linearity.this);
  }

}

@MungoTypestate("Circular")
class CircularObj {

  // :: error: (Object did not complete its protocol. Type: Circular{State0} | Ended | Moved | Null)
  public @MungoNullable CircularObj f = null;

  public void finish() {

  }

}

@MungoTypestate("CircularWithGetter")
class CircularObjWithGetter {

  private @MungoNullable CircularObjWithGetter f = null;

  public void setF(CircularObjWithGetter f) {
    // :: warning: (f: CircularWithGetter{State0})
    // :: error: (Cannot override because object has not ended its protocol. Type: CircularWithGetter{State0} | Null)
    this.f = f;
  }

  public void finish() {
    // :: warning: (f: CircularWithGetter{State0} | Null)
    if (f != null) {
      // :: warning: (f: CircularWithGetter{State0})
      f.finish();
    }
  }

}

// Enforce protocol completeness for objects inside other objects
class PublicLinearityWrapper {
  // :: error: (Object did not complete its protocol. Type: Linearity{State0|State1} | Ended | Moved)
  public Linearity obj = new Linearity();

  public void a() {
    // :: error: (Cannot call a on ended protocol, on moved value, on state State1 (got: State0, State1))
    // :: warning: (obj: Linearity{State0|State1} | Ended | Moved)
    obj.a();
  }

  public void b() {
    // :: error: (Cannot call b on ended protocol, on moved value, on state State0 (got: State0, State1))
    // :: warning: (obj: Linearity{State0|State1} | Ended | Moved)
    obj.b();
  }

  public Linearity get() {
    // :: error: (return.type.incompatible)
    return this.obj;
  }

  public void move1() {
    // :: error: (argument.type.incompatible)
    LinearityTests.use(this.obj);
  }

  public void move2() {
    // :: error: (argument.type.incompatible)
    LinearityTests.use(PublicLinearityWrapper.this.obj);
  }

  public void move3() {
    // :: error: (argument.type.incompatible)
    // :: error: (Returned object did not complete its protocol. Type: Linearity{State0|State1})
    LinearityTests.use(this.get());
  }

  public void move4() {
    // :: error: (argument.type.incompatible)
    // :: error: (Returned object did not complete its protocol. Type: Linearity{State0|State1})
    LinearityTests.use(PublicLinearityWrapper.this.get());
  }
}

class PrivateLinearityWrapper {
  // :: error: (Object did not complete its protocol. Type: Linearity{State0|State1} | Moved | Ended)
  private Linearity obj = new Linearity();

  public void a() {
    // :: error: (Cannot call a on ended protocol, on moved value, on state State1 (got: State0, State1))
    // :: warning: (obj: Linearity{State0|State1} | Moved | Ended)
    obj.a();
  }

  public void b() {
    // :: warning: (obj: Linearity{State0|State1} | Moved | Ended)
    // :: error: (Cannot call b on ended protocol, on moved value, on state State0 (got: State0, State1))
    obj.b();
  }

  public Linearity get() {
    // :: error: (return.type.incompatible)
    return this.obj;
  }

  public void move1() {
    // :: error: (argument.type.incompatible)
    LinearityTests.use(this.obj);
  }

  public void move2() {
    // :: error: (argument.type.incompatible)
    LinearityTests.use(PrivateLinearityWrapper.this.obj);
  }

  public void move3() {
    // :: error: (Returned object did not complete its protocol. Type: Linearity{State0|State1})
    // :: error: (argument.type.incompatible)
    LinearityTests.use(this.get());
  }

  public void move4() {
    // :: error: (Returned object did not complete its protocol. Type: Linearity{State0|State1})
    // :: error: (argument.type.incompatible)
    LinearityTests.use(PrivateLinearityWrapper.this.get());
  }
}

class PrivateLinearityWrapperNoMoves {
  // :: error: (Object did not complete its protocol. Type: Linearity{State0|State1} | Ended)
  private Linearity obj = new Linearity();

  public void a() {
    // :: warning: (obj: Linearity{State0|State1} | Ended)
    // :: error: (Cannot call a on ended protocol, on state State1 (got: State0, State1))
    obj.a();
  }

  public void b() {
    // :: warning: (obj: Linearity{State0|State1} | Ended)
    // :: error: (Cannot call b on ended protocol, on state State0 (got: State0, State1))
    obj.b();
  }
}

class MoveToConstructor {

  // :: error: (Object did not complete its protocol. Type: Linearity{State0|State1})
  public MoveToConstructor(Linearity obj) {

  }

}

class MoveToConstructor2Args {

  // :: error: (Object did not complete its protocol. Type: Linearity{State0|State1})
  public MoveToConstructor2Args(Linearity obj, Linearity obj2) {

  }

}

class MoveToConstructor2 extends MoveToConstructor {

  public MoveToConstructor2(Linearity obj) {
    // :: warning: (obj: Linearity{State0|State1})
    super(obj);
    // :: warning: (obj: Moved)
    // :: error: (Cannot call finish on moved value)
    obj.finish();
  }

}

public class LinearityTests {

  public static void main1() {
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    use(obj);
    // :: warning: (obj: Moved)
    // :: error: (Cannot call finish on moved value)
    obj.finish();
  }

  public static void main1_2() {
    @MungoNullable Linearity obj = null;
    useNullable(null);
    // :: warning: (obj: Null)
    // :: error: (Cannot call finish on null)
    obj.finish();
  }

  public static void main2() {
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    use(obj);
    // :: warning: (obj: Moved)
    // :: error: (argument.type.incompatible)
    use(obj);
  }

  public static void main2_2() {
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    // :: warning: (obj: Moved)
    // :: error: (argument.type.incompatible)
    use2(obj, obj);
    // :: warning: (obj: Moved)
    // :: error: (Cannot call finish on moved value)
    obj.finish();
  }

  public static void main2_3() {
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    // :: warning: (obj: Moved)
    // :: error: (argument.type.incompatible)
    use2((Linearity) ((Linearity) obj), obj);
    // :: warning: (obj: Moved)
    // :: error: (Cannot call finish on moved value)
    obj.finish();
  }

  public static void main3() {
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    Linearity obj2 = obj;
    // :: warning: (obj2: Linearity{State0})
    use(obj2);
    // :: warning: (obj: Moved)
    // :: error: (Cannot call finish on moved value)
    obj.finish();
  }

  public static void main4() {
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    Linearity obj2 = obj;
    // :: warning: (obj2: Linearity{State0})
    use(obj2);
    // :: warning: (obj: Moved)
    // :: error: (argument.type.incompatible)
    use(obj);
  }

  public static void main5() {
    Linearity obj = new Linearity();
    Supplier<String> fn = () -> {
      // :: error: (obj was moved to a different closure)
      // :: warning: (obj: Bottom)
      obj.a();
      return "";
    };
    // :: warning: (obj: Linearity{State0})
    obj.finish();
    fn.get();
  }

  // If an object is moved to a method which we do not have the code for
  public static void main6() {
    List<Linearity> list = new LinkedList<>();
    // :: error: (Passing an object with protocol to a method that cannot be analyzed)
    list.add(new Linearity());
    // :: error: (assignment.type.incompatible)
    Linearity obj1 = list.get(0);
    // :: error: (assignment.type.incompatible)
    Linearity obj2 = list.get(0);
    // :: warning: (obj1: Linearity{State0|State1} | Ended | Moved)
    // :: error: (Cannot call finish on ended protocol, on moved value)
    obj1.finish();
    // :: warning: (obj2: Linearity{State0|State1} | Ended | Moved)
    // :: error: (Cannot call finish on ended protocol, on moved value)
    obj2.finish();
  }

  // Detect moves of objects inside other objects to variables
  public static void main7() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    // :: error: (assignment.type.incompatible)
    Linearity obj = w.obj;
    // :: error: (Cannot call finish on ended protocol, on moved value)
    // :: warning: (obj: Linearity{State0|State1} | Ended | Moved)
    obj.finish();
  }

  // Detect moves of objects inside other objects to methods
  public static void main8() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    // :: error: (argument.type.incompatible)
    use(w.obj);
  }

  // Detect moves of objects inside other objects to other closures
  public static void main9() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    Supplier<String> fn = () -> {
      // :: error: (assignment.type.incompatible)
      Linearity obj = w.obj;
      // :: warning: (obj: Linearity{State0|State1} | Ended | Moved)
      // :: error: (Cannot call finish on ended protocol, on moved value)
      obj.finish();
      return "";
    };
  }

  // Detecting moves to its own method
  public static void main10() {
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    // :: warning: (obj: Moved)
    // :: error: (argument.type.incompatible)
    obj.useOther(obj);
    // :: warning: (obj: Linearity{State0})
    Linearity obj2 = obj;
    // :: warning: (obj2: Linearity{State0})
    obj2.finish();
  }

  // Overrides
  public static void main11() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    // :: error: (Cannot override because object has not ended its protocol. Type: Linearity{State0|State1} | Ended | Moved)
    w.obj = new Linearity();
  }

  // Implicity move in method reference
  public static void main12() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    Supplier<Linearity> method = w::get;
    // :: error: (assignment.type.incompatible)
    Linearity obj = method.get();
    // :: warning: (obj: Linearity{State0|State1} | Ended | Moved)
    // :: error: (Cannot call finish on ended protocol, on moved value)
    obj.finish();
  }

  // Implicity move in method reference
  public static void main13() {
    // :: error: (Object did not complete its protocol. Type: Linearity{State0})
    Linearity obj = new Linearity();
    // :: warning: (obj: Linearity{State0})
    // :: error: (Cannot create reference for method of an object with protocol)
    Runnable method = obj::a;
  }

  public static void main14() {
    Linearity obj1 = new Linearity();
    // :: warning: (obj1: Linearity{State0})
    MoveToConstructor obj2 = new MoveToConstructor(obj1);
    // :: warning: (obj1: Moved)
    // :: error: (Cannot call finish on moved value)
    obj1.finish();
  }

  public static void main15() {
    Linearity obj1 = new Linearity();
    // :: warning: (obj1: Linearity{State0})
    // :: warning: (obj1: Moved)
    // :: error: (argument.type.incompatible)
    MoveToConstructor2Args obj2 = new MoveToConstructor2Args(obj1, obj1);
    // :: warning: (obj1: Moved)
    // :: error: (Cannot call finish on moved value)
    obj1.finish();
  }

  public static void main16() {
    CircularObj o1 = new CircularObj();
    CircularObj o2 = new CircularObj();
    // :: warning: (o1: Circular{State0})
    // :: warning: (o2: Circular{State0})
    // :: error: (Cannot override because object has not ended its protocol. Type: Circular{State0} | Ended | Moved | Null)
    o2.f = o1;
    // :: warning: (o1: Moved)
    // :: warning: (o2: Circular{State0})
    // :: error: (Cannot override because object has not ended its protocol. Type: Circular{State0} | Ended | Moved | Null)
    // :: error: (Cannot access f on moved value)
    o1.f = o2;
  }

  public static void main17() {
    CircularObjWithGetter o1 = new CircularObjWithGetter();
    CircularObjWithGetter o2 = new CircularObjWithGetter();
    // :: warning: (o1: CircularWithGetter{State0})
    // :: warning: (o2: CircularWithGetter{State0})
    o2.setF(o1);
    // :: warning: (o1: Moved)
    // :: warning: (o2: CircularWithGetter{State0})
    // :: error: (Cannot call setF on moved value)
    o1.setF(o2);
  }

  public static void main18() {
    CircularObj o1 = new CircularObj();
    CircularObj o2 = new CircularObj();
    CircularObj o3 = new CircularObj();
    CircularObj o4 = new CircularObj();
    // :: warning: (o3: Circular{State0})
    // :: warning: (o4: Circular{State0})
    // :: error: (Cannot override because object has not ended its protocol. Type: Circular{State0} | Ended | Moved | Null)
    o3.f = o4;
    // :: warning: (o2: Circular{State0})
    // :: warning: (o3: Circular{State0})
    // :: error: (Cannot override because object has not ended its protocol. Type: Circular{State0} | Ended | Moved | Null)
    o2.f = o3;
    // :: warning: (o1: Circular{State0})
    // :: warning: (o2: Circular{State0})
    // :: error: (Cannot override because object has not ended its protocol. Type: Circular{State0} | Ended | Moved | Null)
    o1.f = o2;
    // :: warning: (o4: Moved)
    // :: error: (Cannot call finish on moved value)
    o4.finish();
    // :: warning: (o1: Circular{State0})
    o1.finish();
  }

  // Making sure that the first access marks the object as moved
  // as if it were something like o.setF(o) or Obj#setF(o, o)
  public static void main19() {
    CircularObj o = new CircularObj();
    // :: warning: (o: Circular{State0})
    // :: warning: (o: Moved)
    // :: error: (Cannot override because object has not ended its protocol. Type: Circular{State0} | Ended | Moved | Null)
    o.f = o;
  }

  // Helpers

  public static void use(@MungoRequires("State0") Linearity obj) {
    // :: warning: (obj: Linearity{State0})
    obj.a();
    // :: warning: (obj: Linearity{State1})
    obj.b();
  }

  public static void useNullable(@MungoNullable @MungoRequires("State0") @MungoEnsures("State1") Linearity obj) {
    // :: warning: (obj: Linearity{State0} | Null)
    if (obj != null) {
      // :: warning: (obj: Linearity{State0})
      obj.a();
    }
  }

  public static void useNullable2(@MungoNullable @MungoRequires("State0") @MungoEnsures("State1") Linearity obj) {
    // :: warning: (obj: Linearity{State0} | Null)
    if (obj != null) {
      // :: warning: (obj: Linearity{State0|State1} | Ended | Moved | Null)
      // :: error: (Cannot override because object is not in the state specified by @MungoEnsures. Type: Linearity{State0})
      // :: error: (Cannot override because object has not ended its protocol. Type: Linearity{State0})
      obj = null;
    }
  }

  public static void use2(Linearity obj1, Linearity obj2) {
    // :: warning: (obj1: Linearity{State0|State1})
    obj1.finish();
    // :: warning: (obj2: Linearity{State0|State1})
    obj2.finish();
  }

  public static void useWrapper(PublicLinearityWrapper obj) {
    obj.a();
    obj.b();
  }
}
