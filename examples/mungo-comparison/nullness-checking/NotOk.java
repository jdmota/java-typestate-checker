import jatyc.lib.Nullable;
import jatyc.lib.Requires;

public class NotOk {
  public static void main1(String args[]) {
    @Nullable File f = new File();

    switch (f.open()) {
      case OK:
        System.out.println(f.read());
        f = null;
        f.close();
        break;
      case ERROR:
        break;
    }
  }

  public static void main2(String args[]) {
    use(null);
  }

  public static void use(@Requires("Init") File f) {
    switch (f.open()) {
      case OK:
        System.out.println(f.read());
        f.close();
        break;
      case ERROR:
        break;
    }
  }
}
