public class Main2 {
  public static void dataRace() throws Exception {
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
  }

  /*public static void noDataRace() throws Exception {
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
