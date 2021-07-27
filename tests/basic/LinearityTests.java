import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

import java.util.*;
import java.util.function.*;

@Typestate("Linearity.protocol")
class Linearity {

  public void a() {
  }

  public void b() {
  }

  public void finish() {
  }

  public void useOther(@Requires("State0") Linearity obj) {
    // :: warning: (obj: State{Linearity, State0})
    obj.a();
    // :: warning: (obj: State{Linearity, State1})
    obj.b();
  }

  private void moveThis1() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this);
  }

  private void moveThis2() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(Linearity.this);
  }

}

@Typestate("Circular")
class CircularObj {

  public @Nullable CircularObj f = null;

  public void finish() {

  }

}

@Typestate("CircularWithGetter")
class CircularObjWithGetter {

  private @Nullable CircularObjWithGetter f = null;

  public void setF(@Requires("State0") CircularObjWithGetter f) {
    // :: warning: (f: State{CircularObjWithGetter, State0})
    // :: warning: (this.f: State{CircularObjWithGetter, State0} | Null)
    // :: error: (The previous value of [this.f] did not complete its protocol (found: State{CircularObjWithGetter, State0} | Null))
    this.f = f;
  }

  public void finish() {
    // :: warning: (this.f: State{CircularObjWithGetter, State0} | Null)
    if (f != null) {
      // :: warning: (this.f: State{CircularObjWithGetter, State0})
      f.finish();
    }
  }

}

// Enforce protocol completeness for objects inside other objects
// :: error: ([this.obj] did not complete its protocol (found: Shared{Linearity} | State{Linearity, ?}))
class PublicLinearityWrapper {
  public Linearity obj = new Linearity();

  public void setNull() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot assign because [this.obj] is not accessible here)
    obj = null;
  }

  public void a() {
    // :: error: (Cannot call [a] on Shared{Linearity})
    // :: warning: (this.obj: Shared{Linearity})
    obj.a();
  }

  public void b() {
    // :: error: (Cannot call [b] on Shared{Linearity})
    // :: warning: (this.obj: Shared{Linearity})
    obj.b();
  }

  public Linearity get() {
    // :: warning: (this.obj: Shared{Linearity})
    return this.obj;
  }

  public void move1() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    // :: warning: (this.obj: Shared{Linearity})
    LinearityTests.use(this.obj);
  }

  public void move2() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    // :: warning: (this.obj: Shared{Linearity})
    LinearityTests.use(PublicLinearityWrapper.this.obj);
  }

  public void move3() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this.get());
  }

  public void move4() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(PublicLinearityWrapper.this.get());
  }

  public static void use1(PublicLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PublicLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    LinearityTests.use(wrapper.obj);
  }

  public static void use2(PublicLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PublicLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    wrapper.obj.a();
  }
}

// :: error: ([this.obj] did not complete its protocol (found: Shared{Linearity} | State{Linearity, ?}))
class PrivateLinearityWrapper {
  private Linearity obj = new Linearity();

  public void a() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot call [a] on Shared{Linearity})
    obj.a();
  }

  public void b() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot call [b] on Shared{Linearity})
    obj.b();
  }

  public Linearity get() {
    // :: warning: (this.obj: Shared{Linearity})
    return this.obj;
  }

  public void move1() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this.obj);
  }

  public void move2() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(PrivateLinearityWrapper.this.obj);
  }

  public void move3() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(this.get());
  }

  public void move4() {
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    LinearityTests.use(PrivateLinearityWrapper.this.get());
  }

  public static void use1(PrivateLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PrivateLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    LinearityTests.use(wrapper.obj);
  }

  public static void use2(PrivateLinearityWrapper wrapper) {
    // :: warning: (wrapper: Shared{PrivateLinearityWrapper})
    // :: warning: (wrapper.obj: Unknown)
    // :: error: (Cannot access [wrapper.obj])
    wrapper.obj.a();
  }
}

// :: error: ([this.obj] did not complete its protocol (found: Shared{Linearity} | State{Linearity, ?}))
class PrivateLinearityWrapperNoMoves {
  private Linearity obj = new Linearity();

  public void a() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot call [a] on Shared{Linearity})
    obj.a();
  }

  public void b() {
    // :: warning: (this.obj: Shared{Linearity})
    // :: error: (Cannot call [b] on Shared{Linearity})
    obj.b();
  }
}

class MoveToConstructor {
  // :: error: ([obj] did not complete its protocol (found: State{Linearity, State0} | State{Linearity, State1}))
  public MoveToConstructor(@Requires({"State0", "State1"}) Linearity obj) {

  }
}

class MoveToConstructor2Args {
  // :: error: ([obj] did not complete its protocol (found: State{Linearity, State0} | State{Linearity, State1}))
  // :: error: ([obj2] did not complete its protocol (found: State{Linearity, State0} | State{Linearity, State1}))
  public MoveToConstructor2Args(
    @Requires({"State0", "State1"}) Linearity obj,
    @Requires({"State0", "State1"}) Linearity obj2
  ) {

  }
}

class MoveToConstructor2 extends MoveToConstructor {
  public MoveToConstructor2(@Requires({"State0", "State1"}) Linearity obj) {
    // :: warning: (obj: State{Linearity, State0} | State{Linearity, State1})
    super(obj);
    // :: warning: (obj: Shared{Linearity})
    // :: error: (Cannot call [finish] on Shared{Linearity})
    obj.finish();
  }
}

public class LinearityTests {

  public static void main1() {
    Linearity obj = new Linearity();
    // :: warning: (obj: State{Linearity, State0})
    use(obj);
    // :: warning: (obj: Shared{Linearity})
    // :: error: (Cannot call [finish] on Shared{Linearity})
    obj.finish();
  }

  public static void main1_2() {
    @Nullable Linearity obj = null;
    useNullable(null);
    // :: warning: (obj: Null)
    // :: error: (Cannot call finish on null)
    obj.finish();
  }

  public static void main2() {
    Linearity obj = new Linearity();
    // :: warning: (obj: State{Linearity, State0})
    use(obj);
    // :: warning: (obj: Shared{Linearity})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    use(obj);
  }

  public static void main2_2() {
    Linearity obj = new Linearity();
    // :: warning: (obj: State{Linearity, State0})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0} | State{Linearity, State1})
    use2(obj, obj);
    // :: warning: (obj: Bottom)
    obj.finish();
  }

  public static void main2_3() {
    Linearity obj = new Linearity();
    // :: warning: (obj: State{Linearity, State0})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0} | State{Linearity, State1})
    use2((Linearity) ((Linearity) obj), obj);
    // :: warning: (obj: Bottom)
    obj.finish();
  }

  public static void main3() {
    Linearity obj = new Linearity();
    // :: warning: (obj: State{Linearity, State0})
    Linearity obj2 = obj;
    // :: warning: (obj2: State{Linearity, State0})
    use(obj2);
    // :: warning: (obj: Shared{Linearity})
    // :: error: (Cannot call [finish] on Shared{Linearity})
    obj.finish();
  }

  public static void main4() {
    Linearity obj = new Linearity();
    // :: warning: (obj: State{Linearity, State0})
    Linearity obj2 = obj;
    // :: warning: (obj2: State{Linearity, State0})
    use(obj2);
    // :: warning: (obj: Shared{Linearity})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    use(obj);
  }

  public static void main5() {
    Linearity obj = new Linearity();
    Supplier<String> fn = () -> {
      // :: warning: (obj: Unknown)
      // :: error: (Cannot access [obj])
      obj.a();
      return "";
    };
    // :: warning: (obj: State{Linearity, State0})
    obj.finish();
    // :: warning: (fn: Shared{java.util.function.Supplier})
    fn.get();
  }

  /*public static void main6() {
    List<Linearity> list = new LinkedList<>();
    list.add(new Linearity());
    Linearity obj1 = list.get(0);
    Linearity obj2 = list.get(0);
    obj1.finish();
    obj2.finish();
  }*/

  // Detect moves of objects inside other objects to variables
  public static void main7() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    // :: warning: (w: Shared{PublicLinearityWrapper})
    // :: warning: (w.obj: Unknown)
    // :: error: (Cannot access [w.obj])
    Linearity obj = w.obj;
    // :: warning: (obj: Bottom)
    obj.finish();
  }

  // Detect moves of objects inside other objects to methods
  public static void main8() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    // :: warning: (w.obj: Unknown)
    // :: warning: (w: Shared{PublicLinearityWrapper})
    // :: error: (Cannot access [w.obj])
    use(w.obj);
  }

  // Detect moves of objects inside other objects to other closures
  public static void main9() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    Supplier<String> fn = () -> {
      // :: warning: (w: Unknown)
      // :: warning: (w.obj: Bottom)
      // :: error: (Cannot access [w])
      Linearity obj = w.obj;
      // :: warning: (obj: Bottom)
      obj.finish();
      return "";
    };
  }

  // Detecting moves to its own method
  public static void main10() {
    Linearity obj = new Linearity();
    // :: warning: (obj: State{Linearity, State0})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0})
    obj.useOther(obj);
    // :: warning: (obj: Bottom)
    Linearity obj2 = obj;
    // :: warning: (obj2: Bottom)
    obj2.finish();
  }

  // Overrides
  public static void main11() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    // :: warning: (w: Shared{PublicLinearityWrapper})
    // :: warning: (w.obj: Unknown)
    // :: error: (Cannot assign because [w.obj] is not accessible here)
    // :: error: (Cannot access [w.obj])
    w.obj = new Linearity();
  }

  // Implicity move in method reference
  /*public static void main12() {
    PublicLinearityWrapper w = new PublicLinearityWrapper();
    Supplier<Linearity> method = w::get;
    :: error: (assignment.type.incompatible)
    Linearity obj = method.get();
    :: warning: (obj: State{Linearity, State0} | State{Linearity, State1} | Ended)
    :: error: (Cannot call finish on ended protocol)
    obj.finish();
  }*/

  // Implicity move in method reference
  /*TODO public static void main13() {
    :: error: (Object did not complete its protocol. Type: State{Linearity, State0})
    Linearity obj = new Linearity();
    :: warning: (obj: State{Linearity, State0})
    :: error: (Cannot create reference for method of an object with protocol)
    Runnable method = obj::a;
  }*/

  public static void main14() {
    Linearity obj1 = new Linearity();
    // :: warning: (obj1: State{Linearity, State0})
    MoveToConstructor obj2 = new MoveToConstructor(obj1);
    // :: warning: (obj1: Shared{Linearity})
    // :: error: (Cannot call [finish] on Shared{Linearity})
    obj1.finish();
  }

  public static void main15() {
    Linearity obj1 = new Linearity();
    // :: warning: (obj1: State{Linearity, State0})
    // :: error: (Incompatible parameter: cannot cast from Shared{Linearity} to State{Linearity, State0} | State{Linearity, State1})
    MoveToConstructor2Args obj2 = new MoveToConstructor2Args(obj1, obj1);
    // :: warning: (obj1: Bottom)
    obj1.finish();
  }

  public static void main16() {
    CircularObj o1 = new CircularObj();
    CircularObj o2 = new CircularObj();
    // :: warning: (o1: State{CircularObj, State0})
    // :: warning: (o2: State{CircularObj, State0})
    // :: warning: (o2.f: Unknown)
    // :: error: (Cannot assign because [o2.f] is not accessible here)
    // :: error: (Cannot access [o2.f])
    o2.f = o1;
    // :: warning: (o1: Shared{CircularObj})
    // :: warning: (o2: State{CircularObj, State0})
    // :: warning: (o1.f: Unknown)
    // :: error: (Cannot assign because [o1.f] is not accessible here)
    // :: error: (Cannot access [o1.f])
    o1.f = o2;
  }

  public static void main17() {
    CircularObjWithGetter o1 = new CircularObjWithGetter();
    CircularObjWithGetter o2 = new CircularObjWithGetter();
    // :: warning: (o1: State{CircularObjWithGetter, State0})
    // :: warning: (o2: State{CircularObjWithGetter, State0})
    o2.setF(o1);
    // :: warning: (o1: Shared{CircularObjWithGetter})
    // :: warning: (o2: State{CircularObjWithGetter, State0})
    // :: error: (Cannot call [setF] on Shared{CircularObjWithGetter})
    o1.setF(o2);
  }

  public static void main18() {
    CircularObj o1 = new CircularObj();
    CircularObj o2 = new CircularObj();
    CircularObj o3 = new CircularObj();
    CircularObj o4 = new CircularObj();
    // :: warning: (o3: State{CircularObj, State0})
    // :: warning: (o4: State{CircularObj, State0})
    // :: warning: (o3.f: Unknown)
    // :: error: (Cannot assign because [o3.f] is not accessible here)
    // :: error: (Cannot access [o3.f])
    o3.f = o4;
    // :: warning: (o2: State{CircularObj, State0})
    // :: warning: (o3: State{CircularObj, State0})
    // :: warning: (o2.f: Unknown)
    // :: error: (Cannot assign because [o2.f] is not accessible here)
    // :: error: (Cannot access [o2.f])
    o2.f = o3;
    // :: warning: (o1: State{CircularObj, State0})
    // :: warning: (o2: State{CircularObj, State0})
    // :: warning: (o1.f: Unknown)
    // :: error: (Cannot assign because [o1.f] is not accessible here)
    // :: error: (Cannot access [o1.f])
    o1.f = o2;
    // :: warning: (o4: Shared{CircularObj})
    // :: error: (Cannot call [finish] on Shared{CircularObj})
    o4.finish();
    // :: warning: (o1: State{CircularObj, State0})
    o1.finish();
  }

  public static void main19() {
    CircularObj o = new CircularObj();
    // :: warning: (o: State{CircularObj, State0})
    // :: warning: (o.f: Unknown)
    // :: error: (Cannot assign because [o.f] is not accessible here)
    // :: error: (Cannot access [o.f])
    o.f = o;
  }

  // Helpers

  public static void use(@Requires("State0") Linearity obj) {
    // :: warning: (obj: State{Linearity, State0})
    obj.a();
    // :: warning: (obj: State{Linearity, State1})
    obj.b();
  }

  public static void useNullable(@Nullable @Requires("State0") @Ensures("State1") final Linearity obj) {
    // :: warning: (obj: State{Linearity, State0} | Null)
    if (obj != null) {
      // :: warning: (obj: State{Linearity, State0})
      obj.a();
    }
  }

  // :: error: (Type of parameter [obj] is Shared{Linearity} | Null, expected State{Linearity, State1} | Null})
  public static void useNullable2(@Nullable @Requires("State0") @Ensures("State1") final Linearity obj) {
    // :: warning: (obj: State{Linearity, State0} | Null)
    Linearity obj2 = obj;
    // :: warning: (obj2: State{Linearity, State0} | Null)
    if (obj2 != null) {
      // :: warning: (obj2: State{Linearity, State0})
      // :: error: (The previous value of [obj2] did not complete its protocol (found: State{Linearity, State0}))
      obj2 = null;
    }
  }

  public static void use2(
    @Requires({"State0", "State1"}) Linearity obj1,
    @Requires({"State0", "State1"}) Linearity obj2
  ) {
    // :: warning: (obj1: State{Linearity, State0} | State{Linearity, State1})
    obj1.finish();
    // :: warning: (obj2: State{Linearity, State0} | State{Linearity, State1})
    obj2.finish();
  }

  public static void useWrapper(PublicLinearityWrapper obj) {
    // :: warning: (obj: Shared{PublicLinearityWrapper})
    obj.a();
    // :: warning: (obj: Shared{PublicLinearityWrapper})
    obj.b();
  }
}
