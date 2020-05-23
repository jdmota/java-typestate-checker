import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("ObjWithSetter")
public class ObjWithSetter {

  private @MungoNullable ObjWithSetter f = null;

  public void setF(ObjWithSetter f) {
    this.f = f;
  }

  public void finish() {
    if (f != null) {
      f.finish();
    }
  }

  // Linear chains

  public static void chain1() {
    // o1 -> o2
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    o1.setF(o2);
    o1.finish();
  }

  public static void chain2() {
    // o1 -> o2 -> o3
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    ObjWithSetter o3 = new ObjWithSetter();
    o1.setF(o2);
    // :: error: (Cannot call setF on moved value)
    o2.setF(o3);
    o1.finish();
  }

  public static void chain2Reverse() {
    // o1 -> o2 -> o3
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    ObjWithSetter o3 = new ObjWithSetter();
    o2.setF(o3);
    o1.setF(o2);
    o1.finish();
  }

  // Cycles

  public static void circular1() {
    // o1 -> o1
    ObjWithSetter o1 = new ObjWithSetter();
    // :: error: (argument.type.incompatible)
    o1.setF(o1);
    o1.finish();
  }

  public static void circular2() {
    // o1 -> o2 -> o1
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    o1.setF(o2);
    // :: error: (Cannot call setF on moved value)
    o2.setF(o1);
  }

  public static void circular3() {
    // o1 -> o2 -> o3 -> o1
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    ObjWithSetter o3 = new ObjWithSetter();
    o1.setF(o2);
    // :: error: (Cannot call setF on moved value)
    o2.setF(o3);
    // :: error: (Cannot call setF on moved value)
    o3.setF(o1);
  }

  public static void circular3Reverse() {
    // o1 -> o2 -> o3 -> o1
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    ObjWithSetter o3 = new ObjWithSetter();
    o3.setF(o1);
    o2.setF(o3);
    // :: error: (Cannot call setF on moved value)
    o1.setF(o2);
  }

}
