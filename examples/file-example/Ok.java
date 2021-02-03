public class Ok {
  public static void main(String args[]) {
    File f = new File();

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
