import org.checkerframework.checker.mungo.lib.MungoNullable;

public class Ok {
  public static void main(String args[]) {
    @MungoNullable File f = null;

    if (f != null) {
      switch (f.open()) {
        case OK:
          System.out.println(f.read());
          f.close();
          f = null;
          break;
        case ERROR:
          break;
      }
    }
  }
}
