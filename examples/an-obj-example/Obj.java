import mungo.lib.Typestate;

@Typestate("ObjProtocol")
public class Obj {
  private String str;

  public Obj() {
    this.str = "";
  }

  public void init(String str) {
    this.str = str;
  }

  public String read() {
    return this.str;
  }

  public void close() {

  }
}