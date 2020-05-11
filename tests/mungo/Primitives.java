import org.checkerframework.checker.mungo.lib.MungoNullable;

public class Primitives {

  public static void main1() {
    Integer a = 10;
    int b = a;
  }

  public static void main2() {
    @MungoNullable Integer a = null;
    // :: error: (unboxing.of.nullable)
    // :: warning: (a: Null)
    int b = a;
  }

}
