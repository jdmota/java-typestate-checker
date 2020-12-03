import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.Ensures;
import org.checkerframework.checker.jtc.lib.State;

public class NotOk {

  public static void main() {
    File f = createFile();

    switch (f.open()) {
      case OK:
        f.read();
        read(f);
        f.close();
        break;
      case ERROR:
        break;
    }
  }

  public static @State("Init") File createFile() {
    return new File();
  }

  public static void read(@Requires("Read") @Ensures("Close") File f) {
    f.read();
  }

}
