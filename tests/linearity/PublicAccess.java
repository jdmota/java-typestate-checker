import jatyc.lib.Typestate;

@Typestate("ObjProtocol")
public class PublicAccess {

  public Obj o = new Obj();

  public void finish() {
    o.finish();
  }

  public static void publicAccess() {
    PublicAccess w = new PublicAccess();
    // :: error: (Cannot access [w.o])
    w.o.finish();
    w.finish();
  }

}
