import org.checkerframework.checker.mungo.lib.MungoNullable;

public class NullnessChecks {

  public Object obj = new Object();

  public static void main1() {
    @MungoNullable NullnessChecks n = null;
    // :: warning: (n: Null)
    // :: error: (dereference.of.nullable)
    System.out.println(n.obj);
  }

  public static void main2() {
    @MungoNullable NullnessChecks n = null;
    // :: warning: (n: Null)
    // :: warning: (cast.unsafe)
    System.out.println((Object) n);
  }

  public static void main3() {
    // :: error: (assignment.type.incompatible)
    NullnessChecks n = null;
  }

  // https://github.com/typetools/checker-framework/issues/3267

  // :: error: (Object did not complete its protocol. Type: Object | Null)
  public static void foo(@MungoNullable Object obj) {
    // :: warning: (obj: Object | Null)
    if ((obj != null) == false) {
      // :: warning: (obj: Object | Null)
      // :: error: (Cannot call toString on object, on null)
      obj.toString();
    }
  }

  // :: error: (Object did not complete its protocol. Type: Object | Null)
  public static void bar(@MungoNullable Object obj) {
    // :: warning: (obj: Object | Null)
    if (!(obj == null) == false) {
      // :: warning: (obj: Object | Null)
      // :: error: (Cannot call toString on object, on null)
      obj.toString();
    }
  }

  // :: error: (Object did not complete its protocol. Type: Null | Object)
  public static void baz(@MungoNullable Object obj) {
    // :: warning: (obj: Object | Null)
    if ((obj == null) == true) {
      // :: warning: (obj: Null | Object)
      // :: error: (Cannot call toString on object, on null)
      obj.toString();
    }
  }

}
