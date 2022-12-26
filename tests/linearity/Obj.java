import jatyc.lib.Typestate;
import jatyc.lib.Requires;

@Typestate("ObjProtocol")
public class Obj {

  public void finish() {

  }

  public static void move1() {
    Obj obj = new Obj();
    use(obj);
    // :: error: (Cannot call [finish] on Shared{Obj})
    obj.finish();
  }

  public static void move2() {
    Obj obj1 = new Obj();
    Obj obj2 = new Obj();
    use(obj1, obj2);
    // :: error: (Cannot call [finish] on Shared{Obj})
    obj1.finish();
    // :: error: (Cannot call [finish] on Shared{Obj})
    obj2.finish();
  }

  public static void moveTwice() {
    Obj obj = new Obj();
    // :: error: (Incompatible parameter: cannot cast from Shared{Obj} to State{Obj, Start})
    use(obj, obj);
    obj.finish();
  }

  // Helpers

  public static void use(@Requires("Start") Obj obj) {
    obj.finish();
  }

  public static void use(@Requires("Start") Obj obj1, @Requires("Start") Obj obj2) {
    obj1.finish();
    obj2.finish();
  }

}
