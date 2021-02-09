public class Main1 {
  /*public static void ok() throws Exception {
    LineReader reader = new LineReader();

    switch (reader.open("LineReader.java")) {
      case OK:
        while (!reader.eof()) {
          System.out.println(reader.read());
        }
        reader.close();
        break;
      case ERROR:
        System.err.println("Could not open file");
        break;
    }
  }*/

  public static void notOk() throws Exception {
    LineReader reader = new LineReader();

    switch (reader.open("LineReader.java")) {
      case OK:
        while (reader.eof()) {
          System.out.println(reader.read());
        }
        break;
      case ERROR:
        System.err.println("Could not open file");
        break;
    }
  }
}
