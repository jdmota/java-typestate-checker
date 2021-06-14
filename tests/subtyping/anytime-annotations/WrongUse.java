import jatyc.lib.Anytime;
import jatyc.lib.NotAnytime;

public class WrongUse {

  public WrongUse() {

  }

  @NotAnytime
  // :: error: (@Anytime and @NotAnytime annotations do not apply to constructors/static/protected/private methods)
  private void m1() {

  }

  @NotAnytime
  // :: error: (@Anytime and @NotAnytime annotations do not apply to constructors/static/protected/private methods)
  public static void m2() {

  }

  @Anytime @NotAnytime
  // :: error: (@Anytime and @NotAnytime annotations should not be used in the same method)
  public void m3() {

  }

  @Anytime
  // :: warning: (Redundant use of @Anytime annotation in method of class without protocol)
  public void m4() {

  }

}
