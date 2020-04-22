import org.checkerframework.checker.mungo.lib.MungoNullable;

public class Ok {
  public static void main(String args[]) {
    @MungoNullable File f = args.length > 0 ? null : new File();

    if (f == null) {
      f = new File();
    }

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
