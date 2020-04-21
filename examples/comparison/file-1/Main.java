public class Main {

  public static void main(String[] args) {
    File f = new File();

    switch (f.open()) {
      case OK:
        while (!f.eof()) {
          f.read();
        }
        f.close();
        break;
      case ERROR:
        break;
    }
  }

}
