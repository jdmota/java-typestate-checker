import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("Obj")
public class PrivateAccess {

  private Obj o = new Obj();

  public void finish() {
    // FIXME issue here, we are not aware that privateAccess() broke our assumptions...
    // and the object already finished...
    o.finish();
  }

  public static void privateAccess() {
    PrivateAccess w = new PrivateAccess();
    // :: error: (Cannot call finish on ended protocol, on moved value)
    w.o.finish();
    w.finish();
  }

}
