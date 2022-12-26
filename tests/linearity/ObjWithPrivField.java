import jatyc.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("ObjWithPrivField")
public class ObjWithPrivField {

  private @Nullable ObjWithPrivField f = null;

  public void finish() {
    if (f != null) {
      f.finish();
    }
  }

  // Linear chains

  public static void chain1() {
    // o1 -> o2
    ObjWithPrivField o1 = new ObjWithPrivField();
    ObjWithPrivField o2 = new ObjWithPrivField();
    // :: error: (Cannot access [o1.f])
    // :: error: (Cannot assign because [o1.f] is not accessible here)
    o1.f = o2;
    o1.finish();
  }

}
