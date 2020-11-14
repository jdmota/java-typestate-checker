import org.checkerframework.checker.mungo.lib.MungoRequires;
import org.checkerframework.checker.mungo.lib.MungoEnsures;
import org.checkerframework.checker.mungo.lib.MungoState;

public class Ok {

  public static void main() {
    File f = createFile();

    switch (f.open()) {
      case OK:
        read(f);
        f.close();
        break;
      case ERROR:
        break;
    }
  }
  
  public static @MungoState("Init") File createFile() {
    return new File();
  }

  public static void read(@MungoRequires("Read") @MungoEnsures("Close") File f) {
    f.read();
  }

}
