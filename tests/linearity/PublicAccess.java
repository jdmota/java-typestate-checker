import mungo.lib.Typestate;

@Typestate("ObjProtocol")
public class PublicAccess {

  // :: error: (Object did not complete its protocol. Type: Unknown)
  public Obj o = new Obj();

  public void finish() {
    // :: error: (Cannot call finish on unknown)
    o.finish();
  }

  public static void publicAccess() {
    PublicAccess w = new PublicAccess();
    // :: error: (Cannot call finish on unknown)
    w.o.finish();
    w.finish();
  }

}
