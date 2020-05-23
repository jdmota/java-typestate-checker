import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

public class PrivateAccessIssue {

  @Typestate("Obj")
  public static class Wrapper {

    private Obj o = new Obj();

    public void finish() {
      // TODO issue here, we are not aware that privateAccess() broke our assumptions...
      // and the object already finished...
      o.finish();
    }

    // Private access

    public static void privateAccess() {
      Wrapper w = new Wrapper();
      // :: error: (Cannot call finish on ended protocol, on moved value)
      w.o.finish();
      w.finish();
    }

  }

}
