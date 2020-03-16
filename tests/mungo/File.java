import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("File.protocol")
class File {

  public enum Status {
    OK, ERROR
  }

  public Status open() {
    return Status.OK;
  }

  public boolean hasNext() {
    return false;
  }

  public int read() {
    return -1;
  }

  public void close() {
  }

  public static void main(String[] args) {

    File f = new File();

    switch (f.open()) {
      case OK:
        while (f.hasNext()) {
          f.read();
        }
        f.close();
        break;
      case ERROR:
        break;
    }

  }

}
