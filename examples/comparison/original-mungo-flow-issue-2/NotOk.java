public class NotOk {
  public static void main(String args[]) {
    File f = new File();

    switch (f.open()) {
      case OK:
        switch (f.read()) {
          case "CLOSE":
            f.close();
            break;
        }
        break;
      case ERROR:
        break;
    }
  }
}
