import jatyc.lib.Typestate;
import jatyc.lib.Nullable;
import jatyc.lib.Requires;

@Typestate("ObjWithSetter")
public class ObjWithSetter {

  private @Nullable ObjWithSetter f = null;

  public void setF(@Requires({"Start", "Set"}) ObjWithSetter f) {
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
    // :: error: (Cannot call [setF] on Shared{ObjWithSetter})
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
    // :: error: (Incompatible parameter: cannot cast from Shared{ObjWithSetter} to State{ObjWithSetter, Set})
    o1.setF(o1);
    o1.finish();
  }

  public static void circular2() {
    // o1 -> o2 -> o1
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    o1.setF(o2);
    // :: error: (Cannot call [setF] on Shared{ObjWithSetter})
    o2.setF(o1);
  }

  public static void circular3() {
    // o1 -> o2 -> o3 -> o1
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    ObjWithSetter o3 = new ObjWithSetter();
    o1.setF(o2);
    // :: error: (Cannot call [setF] on Shared{ObjWithSetter})
    o2.setF(o3);
    // :: error: (Cannot call [setF] on Shared{ObjWithSetter})
    o3.setF(o1);
  }

  public static void circular3Reverse() {
    // o1 -> o2 -> o3 -> o1
    ObjWithSetter o1 = new ObjWithSetter();
    ObjWithSetter o2 = new ObjWithSetter();
    ObjWithSetter o3 = new ObjWithSetter();
    o3.setF(o1);
    o2.setF(o3);
    // :: error: (Cannot call [setF] on Shared{ObjWithSetter})
    o1.setF(o2);
  }

  // Complex examples

  public static void main(String[] args) {
    createChainOk(new ObjWithSetter(), 10);
    createChainNotOk(new ObjWithSetter(), 10);
  }

  public static void createChainOk(@Requires({"Start", "Set"}) ObjWithSetter o2, int len) {
    if (len > 0) {
      ObjWithSetter o1 = new ObjWithSetter();
      o1.setF(o2);
      createChainOk(o1, len - 1);
    } else {
      o2.finish();
    }
  }

  // :: error: ([o1] did not complete its protocol (found: State{ObjWithSetter, Set}))
  public static void createChainNotOk(@Requires({"Start", "Set"}) ObjWithSetter o2, int len) {
    if (len > 0) {
      ObjWithSetter o1 = new ObjWithSetter();
      o1.setF(o2);
      // :: error: (Incompatible parameter: cannot cast from Shared{ObjWithSetter} to State{ObjWithSetter, Set})
      createChainNotOk(o2, len - 1);
    } else {
      o2.finish();
    }
  }

}
