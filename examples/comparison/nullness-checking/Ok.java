import org.checkerframework.checker.jtc.lib.Nullable;
import org.checkerframework.checker.jtc.lib.Requires;

public class Ok {
  public static void main(String args[]) {
    @Nullable File f = args.length == 0 ? null : new File();

    if (f != null) {
      use(f);
    }
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
