import org.checkerframework.checker.jtc.lib.Nullable;

public class Primitives {

  public static void main1() {
    Integer a = 10;
    int b = a;
  }

  public static void main2() {
    @Nullable Integer a = null;
    // :: error: (unboxing.of.nullable)
    // :: warning: (a: Null)
    int b = a;
  }

}
