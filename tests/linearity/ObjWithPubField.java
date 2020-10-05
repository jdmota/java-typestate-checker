import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("ObjWithPubField")
public class ObjWithPubField {

  // :: error: (Object did not complete its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
  public @MungoNullable ObjWithPubField f = null;

  public void finish() {
    if (f != null) {
      // :: error: (Cannot call finish on ended protocol, on moved value)
      f.finish();
    }
  }

  // Linear chains

  public static void chain1() {
    // o1 -> o2
    ObjWithPubField o1 = new ObjWithPubField();
    ObjWithPubField o2 = new ObjWithPubField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o1.f = o2;
    o1.finish();
  }

  public static void chain2() {
    // o1 -> o2 -> o3
    ObjWithPubField o1 = new ObjWithPubField();
    ObjWithPubField o2 = new ObjWithPubField();
    ObjWithPubField o3 = new ObjWithPubField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o1.f = o2;
    // :: error: (Cannot access f on moved value)
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o2.f = o3;
    o1.finish();
  }

  public static void chain2Reverse() {
    // o1 -> o2 -> o3
    ObjWithPubField o1 = new ObjWithPubField();
    ObjWithPubField o2 = new ObjWithPubField();
    ObjWithPubField o3 = new ObjWithPubField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o2.f = o3;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o1.f = o2;
    o1.finish();
  }

  // Cycles

  public static void circular1() {
    // o1 -> o1
    ObjWithPubField o1 = new ObjWithPubField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o1.f = o1;
    // :: error: (Cannot call finish on moved value)
    o1.finish();
  }

  public static void circular2() {
    // o1 -> o2 -> o1
    ObjWithPubField o1 = new ObjWithPubField();
    ObjWithPubField o2 = new ObjWithPubField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o1.f = o2;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    // :: error: (Cannot access f on moved value)
    o2.f = o1;
  }

  public static void circular3() {
    // o1 -> o2 -> o3 -> o1
    ObjWithPubField o1 = new ObjWithPubField();
    ObjWithPubField o2 = new ObjWithPubField();
    ObjWithPubField o3 = new ObjWithPubField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o1.f = o2;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    // :: error: (Cannot access f on moved value)
    o2.f = o3;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    // :: error: (Cannot access f on moved value)
    o3.f = o1;
  }

  public static void circular3Reverse() {
    // o1 -> o2 -> o3 -> o1
    ObjWithPubField o1 = new ObjWithPubField();
    ObjWithPubField o2 = new ObjWithPubField();
    ObjWithPubField o3 = new ObjWithPubField();
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o3.f = o1;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    o2.f = o3;
    // :: error: (Cannot override because object has not ended its protocol. Type: ObjWithPubField{Start} | Ended | Null | Moved)
    // :: error: (Cannot access f on moved value)
    o1.f = o2;
  }

}
