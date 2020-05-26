import mungo.lib.Typestate;

@Typestate("ObjProtocol")
public class Obj {

  public void finish() {

  }

  public static void move1() {
    Obj obj = new Obj();
    use(obj);
    // :: error: (Cannot call finish on moved value)
    obj.finish();
  }

  public static void move2() {
    Obj obj1 = new Obj();
    Obj obj2 = new Obj();
    use(obj1, obj2);
    // :: error: (Cannot call finish on moved value)
    obj1.finish();
    // :: error: (Cannot call finish on moved value)
    obj2.finish();
  }

  public static void moveTwice() {
    Obj obj = new Obj();
    // :: error: (argument.type.incompatible)
    use(obj, obj);
    // :: error: (Cannot call finish on moved value)
    obj.finish();
  }

  // Helpers

  public static void use(Obj obj) {
    obj.finish();
  }

  public static void use(Obj obj1, Obj obj2) {
    obj1.finish();
    obj2.finish();
  }

}
