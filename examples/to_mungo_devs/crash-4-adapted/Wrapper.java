import mungo.lib.Typestate;

@Typestate("ObjProtocol")
public class Wrapper {

  private Obj o = new Obj();

  public void finish() {
    o.finish();
  }

  public static void main() {
    Wrapper w = new Wrapper();
    // w.o.finish();
    w.finish();
  }

}
