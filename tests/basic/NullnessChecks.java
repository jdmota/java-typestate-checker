import jatyc.lib.Nullable;

public class NullnessChecks {

  public String obj = new String("some text");

  public static void main1() {
    NullnessChecks n = null;
    // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
    // :: warning: (n: Null)
    // :: warning: (n.obj: Bottom)
    // :: error: (Cannot access field [obj] of null)
    System.out.println(n.obj);
  }

  public static void main2() {
    NullnessChecks n = null;
    // :: warning: (n: Null)
    Object obj = (Object) n;
  }

  public static void main3() {
    NullnessChecks n = null;
  }

  public static void main4() {
    NullnessChecks n = new NullnessChecks();
    // :: warning: (n: Shared{NullnessChecks})
    if (n == null) {
      // :: warning: (n: Bottom)
      // :: warning: (n.obj: Bottom)
      // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
      System.out.println(n.obj);
    }
  }

  // https://github.com/typetools/checker-framework/issues/3267

  public static void foo(@Nullable String obj) {
    // :: warning: (obj: Shared{java.lang.String} | Null)
    if ((obj != null) == false) {
      // :: warning: (obj: Null)
      // :: error: (Cannot call [toString] on null (found: Null))
      obj.toString();
    }
  }

  public static void bar(@Nullable String obj) {
    // :: warning: (obj: Shared{java.lang.String} | Null)
    if (!(obj == null) == false) {
      // :: warning: (obj: Null)
      // :: error: (Cannot call [toString] on null (found: Null))
      obj.toString();
    }
  }

  public static void baz(@Nullable String obj) {
    // :: warning: (obj: Shared{java.lang.String} | Null)
    if ((obj == null) == true) {
      // :: warning: (obj: Null)
      // :: error: (Cannot call [toString] on null (found: Null))
      obj.toString();
    }
  }

  public class WithoutProtocol {
    public String str;

    public void action1() {
      // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
      // :: warning: (this.str: Shared{java.lang.String} | Null)
      // :: error: (Cannot call [toUpperCase] on null (found: Shared{java.lang.String} | Null))
      System.out.println(str.toUpperCase());
    }

    public void action2() {
      String str = null;
      // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
      // :: warning: (str: Null)
      System.out.print(str);
      // :: warning: (java.lang.System.out: Shared{java.io.PrintStream})
      // :: warning: (str: Null)
      System.out.println(str);
    }
  }

}
