import org.checkerframework.checker.mungo.lib.MungoNullable;
import org.checkerframework.checker.mungo.lib.MungoState;

public class Ok {
  public static void main(String args[]) {
    @MungoNullable File f = args.length == 0 ? null : new File();

    if (f != null) {
      use(f);
    }
  }
  
  public static void use(@MungoState("Init") File f) {
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
