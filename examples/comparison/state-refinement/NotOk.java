import org.checkerframework.checker.mungo.lib.MungoRequires;

public class NotOk {

  public static void main() {
    File f = new File();

    switch (f.open()) {
      case OK:
        use(f);
        break;
      case ERROR:
        break;
    }
  }

  public static void use(@MungoRequires("Close") File f) {
    f.read();
    f.close();
  }

}
