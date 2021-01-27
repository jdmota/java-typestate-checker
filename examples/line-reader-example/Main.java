public class Main {
  /*public static void main(String[] args) {
    String demo = args[0];

    try {
      switch(demo) {
        case "ok":
          ok();
          break;
        case "ok2":
          ok2();
          break;
        case "nullPointer":
        case "null-pointer":
          nullPointer();
          break;
        case "closeError":
        case "close-error":
          closeError();
          break;
        case "dataRace":
        case "data-race":
          dataRace();
          break;
        case "dataRace2":
        case "data-race-2":
          dataRace2();
          break;
        default:
          System.err.println("Demo " + demo + " not available");
      }
    } catch (Exception exp) {
      exp.printStackTrace();
    }
  }*/

  // No errors
  public static void ok() throws Exception {
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
  }

  // java.lang.NullPointerException
  /*public static void nullPointer() throws Exception {
    LineReader reader = new LineReader();

    while (!reader.eof()) {
      System.out.println(reader.read());
    }
    reader.close();
  }*/
  
  // Errors
  public static void mistakes() throws Exception {
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

  // java.io.IOException: Stream closed
  public static void closeError() throws Exception {
    LineReader reader = new LineReader();

    switch (reader.open("LineReader.java")) {
      case OK:
        reader.close();
        while (!reader.eof()) {
          System.out.println(reader.read());
        }
        break;
      case ERROR:
        System.err.println("Could not open file");
        break;
    }
  }

  // java.io.IOException: Stream closed
  /*public static void dataRace() throws Exception {
    LineReader reader = new LineReader();

    if (reader.open("LineReader.java") == Status.OK) {
      Thread thread = new Thread(() -> {try{
        while (!reader.eof()) {
          System.out.println(reader.read());
        }
      }catch(Exception exp){System.err.println("In thread:");exp.printStackTrace();}});

      thread.start();

      reader.close();

      thread.join();
    } else {
      System.err.println("Could not open file");
    }
  }*/

  // Hidden error
  /*public static void dataRace2() throws Exception {
    LineReader reader = new LineReader();

    if (reader.open("LineReader.java") == Status.OK) {
      Thread thread = new Thread(() -> {try{
        while (!reader.eof()) {
          System.out.println(reader.read());
        }
      }catch(Exception exp){System.err.println("In thread:");exp.printStackTrace();}});

      thread.start();

      while (!reader.eof()) {
        reader.read();
      }

      thread.join();
    } else {
      System.err.println("Could not open file");
    }
  }*/

  // No errors
  /*public static void ok2() throws Exception {
    LineReader reader = new LineReader();

    if (reader.open("LineReader.java") == Status.OK) {
      Thread thread = new Thread(() -> {try{
        while (!reader.eof()) {
          System.out.println(reader.read());
        }
      }catch(Exception exp){System.err.println("In thread:");exp.printStackTrace();}});

      thread.start();

      thread.join();

      reader.close();
    } else {
      System.err.println("Could not open file");
    }
  }*/
}
