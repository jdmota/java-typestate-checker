import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("ObjWithPubField")
public class ObjWithPubField {

  public @Nullable ObjWithPubField f = null;

  public void finish() {
    if (f != null) {
      f.finish();
    }
  }

  // Linear chains

  public static void chain1() {
    // o1 -> o2
    ObjWithPubField o1 = new ObjWithPubField();
    ObjWithPubField o2 = new ObjWithPubField();
    // :: error: (Cannot access [o1.f])
    // :: error: (Cannot assign because [o1.f] is not accessible here)
    o1.f = o2;
    o1.finish();
  }

}
