import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("ObjWithPrivField")
public class ObjWithPrivField {

  private @MungoNullable ObjWithPrivField f = null;

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
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o1.f = o2;
    o1.finish();
  }

  public static void chain2() {
    // o1 -> o2 -> o3
    ObjWithPrivField o1 = new ObjWithPrivField();
    ObjWithPrivField o2 = new ObjWithPrivField();
    ObjWithPrivField o3 = new ObjWithPrivField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o1.f = o2;
    // :: error: (Cannot access f on moved value)
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o2.f = o3;
    o1.finish();
  }

  public static void chain2Reverse() {
    // o1 -> o2 -> o3
    ObjWithPrivField o1 = new ObjWithPrivField();
    ObjWithPrivField o2 = new ObjWithPrivField();
    ObjWithPrivField o3 = new ObjWithPrivField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o2.f = o3;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o1.f = o2;
    o1.finish();
  }

  // Cycles

  public static void circular1() {
    // o1 -> o1
    ObjWithPrivField o1 = new ObjWithPrivField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o1.f = o1;
    // :: error: (Cannot call finish on moved value)
    o1.finish();
  }

  public static void circular2() {
    // o1 -> o2 -> o1
    ObjWithPrivField o1 = new ObjWithPrivField();
    ObjWithPrivField o2 = new ObjWithPrivField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o1.f = o2;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    // :: error: (Cannot access f on moved value)
    o2.f = o1;
  }

  public static void circular3() {
    // o1 -> o2 -> o3 -> o1
    ObjWithPrivField o1 = new ObjWithPrivField();
    ObjWithPrivField o2 = new ObjWithPrivField();
    ObjWithPrivField o3 = new ObjWithPrivField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o1.f = o2;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    // :: error: (Cannot access f on moved value)
    o2.f = o3;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    // :: error: (Cannot access f on moved value)
    o3.f = o1;
  }

  public static void circular3Reverse() {
    // o1 -> o2 -> o3 -> o1
    ObjWithPrivField o1 = new ObjWithPrivField();
    ObjWithPrivField o2 = new ObjWithPrivField();
    ObjWithPrivField o3 = new ObjWithPrivField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o3.f = o1;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    o2.f = o3;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPrivField{Start} | Ended | Moved | Null)
    // :: error: (Cannot access f on moved value)
    o1.f = o2;
  }

}
