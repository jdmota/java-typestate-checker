public class Main {
  public static void main(String args[]) {
    File f = new File();

    switch (f.open()) {
      case OK:
        switch (f.read()) {
          case "CLOSE":
            f.close();
            break;
        }
        // File might not close
        break;
      case ERROR:
        break;
    }
  }
}
