public class Main {
  public static void main(String args[]) throws Exception { // error: [reader] did not complete its protocol
    LineReader reader = new LineReader();

    switch (reader.open("LineReader.java")) {
      case OK:
        while (reader.eof()) {
          System.out.println(reader.read()); // error: Cannot call [read] on State{LineReader, Close}
        }
        break;
      case ERROR:
        System.err.println("Could not open file");
        break;
    }
  }
}
