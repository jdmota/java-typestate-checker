import mungo.lib.Typestate;
import org.checkerframework.checker.mungo.lib.MungoNullable;

@Typestate("ObjProtocol")
public class PublicAccess {
  
  // :: error: (Object did not complete its protocol. Type: Obj{Start} | Ended | Moved)
  public Obj o = new Obj();

  public void finish() {
    // :: error: (Cannot call finish on ended protocol, on moved value)
    o.finish();
  }

  public static void publicAccess() {
    PublicAccess w = new PublicAccess();
    // :: error: (Cannot call finish on ended protocol, on moved value)
    w.o.finish();
    w.finish();
  }

}
