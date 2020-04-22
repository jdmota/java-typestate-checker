public class NotOk {
  public static void main(String args[]) {
    File f = new File();

    switch (f.open()) {
      case ERROR:
        System.out.println(f.read());
        f.close();
        break;
      case OK:
        break;
    }
  }
}
