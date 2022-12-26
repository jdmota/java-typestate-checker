import jatyc.lib.Typestate;

@Typestate("ObjProtocol")
public class PrivateAccess {

  private Obj o = new Obj();

  public void finish() {
    o.finish();
  }

  public static void privateAccess() {
    PrivateAccess w = new PrivateAccess();
    // :: error: (Cannot access [w.o])
    w.o.finish();
    w.finish();
  }

}
