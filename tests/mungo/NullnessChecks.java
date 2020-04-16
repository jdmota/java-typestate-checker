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

}
