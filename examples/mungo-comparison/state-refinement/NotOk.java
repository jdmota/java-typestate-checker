import jatyc.lib.Requires;
import jatyc.lib.Ensures;

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

  public static @Ensures("Init") File createFile() {
    return new File();
  }

  public static void read(@Requires("Read") @Ensures("Close") final File f) {
    f.read();
  }

}
